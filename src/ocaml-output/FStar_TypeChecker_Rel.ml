open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____60266 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____60301 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list ;
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
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list)
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
  worklist -> FStar_TypeChecker_Env.implicits) =
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
                    let uu____60724 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____60724;
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
                       FStar_TypeChecker_Env.imp_reason = reason;
                       FStar_TypeChecker_Env.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Env.imp_tm = t;
                       FStar_TypeChecker_Env.imp_range = r
                     }  in
                   (ctx_uvar, t,
                     (let uu___656_60756 = wl  in
                      {
                        attempting = (uu___656_60756.attempting);
                        wl_deferred = (uu___656_60756.wl_deferred);
                        ctr = (uu___656_60756.ctr);
                        defer_ok = (uu___656_60756.defer_ok);
                        smt_ok = (uu___656_60756.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_60756.umax_heuristic_ok);
                        tcenv = (uu___656_60756.tcenv);
                        wl_implicits = (imp :: (wl.wl_implicits))
                      })))
  
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
            let uu___662_60789 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_60789.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_60789.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_60789.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_60789.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_60789.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_60789.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_60789.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_60789.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_60789.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_60789.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_60789.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_60789.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_60789.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_60789.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_60789.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_60789.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_60789.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_60789.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_60789.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_60789.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_60789.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_60789.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_60789.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_60789.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_60789.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_60789.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_60789.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_60789.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_60789.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_60789.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_60789.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_60789.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_60789.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_60789.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_60789.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_60789.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_60789.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_60789.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_60789.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_60789.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_60789.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_60789.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____60791 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____60791 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____60834 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____60870 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____60903 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____60914 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____60925 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_60943  ->
    match uu___585_60943 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____60955 = FStar_Syntax_Util.head_and_args t  in
    match uu____60955 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____61018 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____61020 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____61035 =
                     let uu____61037 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____61037  in
                   FStar_Util.format1 "@<%s>" uu____61035
                in
             let uu____61041 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____61018 uu____61020 uu____61041
         | uu____61044 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_61056  ->
      match uu___586_61056 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____61061 =
            let uu____61065 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____61067 =
              let uu____61071 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____61073 =
                let uu____61077 =
                  let uu____61081 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____61081]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____61077
                 in
              uu____61071 :: uu____61073  in
            uu____61065 :: uu____61067  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____61061
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61092 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____61094 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____61096 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____61092
            uu____61094 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____61096
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_61110  ->
      match uu___587_61110 with
      | UNIV (u,t) ->
          let x =
            let uu____61116 = FStar_Options.hide_uvar_nums ()  in
            if uu____61116
            then "?"
            else
              (let uu____61123 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____61123 FStar_Util.string_of_int)
             in
          let uu____61127 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____61127
      | TERM (u,t) ->
          let x =
            let uu____61134 = FStar_Options.hide_uvar_nums ()  in
            if uu____61134
            then "?"
            else
              (let uu____61141 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____61141 FStar_Util.string_of_int)
             in
          let uu____61145 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____61145
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____61164 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____61164 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____61185 =
      let uu____61189 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____61189
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____61185 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____61208 .
    (FStar_Syntax_Syntax.term * 'Auu____61208) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____61227 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____61248  ->
              match uu____61248 with
              | (x,uu____61255) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____61227 (FStar_String.concat " ")
  
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
        (let uu____61298 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____61298
         then
           let uu____61303 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____61303
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_61314  ->
    match uu___588_61314 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____61320 .
    'Auu____61320 FStar_TypeChecker_Common.problem ->
      'Auu____61320 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_61332 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_61332.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_61332.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_61332.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_61332.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_61332.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_61332.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_61332.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____61340 .
    'Auu____61340 FStar_TypeChecker_Common.problem ->
      'Auu____61340 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_61360  ->
    match uu___589_61360 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61366  -> FStar_TypeChecker_Common.TProb _61366)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61372  -> FStar_TypeChecker_Common.CProb _61372)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_61378  ->
    match uu___590_61378 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_61384 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_61384.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_61384.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_61384.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_61384.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_61384.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_61384.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_61384.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_61384.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_61384.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_61392 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_61392.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_61392.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_61392.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_61392.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_61392.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_61392.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_61392.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_61392.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_61392.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_61405  ->
      match uu___591_61405 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_61412  ->
    match uu___592_61412 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_61425  ->
    match uu___593_61425 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_61440  ->
    match uu___594_61440 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_61455  ->
    match uu___595_61455 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_61469  ->
    match uu___596_61469 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_61483  ->
    match uu___597_61483 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_61495  ->
    match uu___598_61495 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____61511 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____61511) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____61541 =
          let uu____61543 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61543  in
        if uu____61541
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____61580)::bs ->
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
          let uu____61627 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61651 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61651]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61627
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61679 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61703 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61703]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61679
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____61750 =
          let uu____61752 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61752  in
        if uu____61750
        then ()
        else
          (let uu____61757 =
             let uu____61760 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____61760
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____61757 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____61809 =
          let uu____61811 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61811  in
        if uu____61809
        then ()
        else
          (let uu____61816 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____61816)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____61836 =
        let uu____61838 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____61838  in
      if uu____61836
      then ()
      else
        (let msgf m =
           let uu____61852 =
             let uu____61854 =
               let uu____61856 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____61856 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____61854  in
           Prims.op_Hat msg uu____61852  in
         (let uu____61861 = msgf "scope"  in
          let uu____61864 = p_scope prob  in
          def_scope_wf uu____61861 (p_loc prob) uu____61864);
         (let uu____61876 = msgf "guard"  in
          def_check_scoped uu____61876 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____61883 = msgf "lhs"  in
                def_check_scoped uu____61883 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61886 = msgf "rhs"  in
                def_check_scoped uu____61886 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____61893 = msgf "lhs"  in
                def_check_scoped_comp uu____61893 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61896 = msgf "rhs"  in
                def_check_scoped_comp uu____61896 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_61917 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_61917.wl_deferred);
          ctr = (uu___831_61917.ctr);
          defer_ok = (uu___831_61917.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_61917.umax_heuristic_ok);
          tcenv = (uu___831_61917.tcenv);
          wl_implicits = (uu___831_61917.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____61925 .
    FStar_TypeChecker_Env.env ->
      ('Auu____61925 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_61948 = empty_worklist env  in
      let uu____61949 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____61949;
        wl_deferred = (uu___835_61948.wl_deferred);
        ctr = (uu___835_61948.ctr);
        defer_ok = (uu___835_61948.defer_ok);
        smt_ok = (uu___835_61948.smt_ok);
        umax_heuristic_ok = (uu___835_61948.umax_heuristic_ok);
        tcenv = (uu___835_61948.tcenv);
        wl_implicits = (uu___835_61948.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_61972 = wl  in
        {
          attempting = (uu___840_61972.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_61972.ctr);
          defer_ok = (uu___840_61972.defer_ok);
          smt_ok = (uu___840_61972.smt_ok);
          umax_heuristic_ok = (uu___840_61972.umax_heuristic_ok);
          tcenv = (uu___840_61972.tcenv);
          wl_implicits = (uu___840_61972.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_62000 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_62000.wl_deferred);
         ctr = (uu___845_62000.ctr);
         defer_ok = (uu___845_62000.defer_ok);
         smt_ok = (uu___845_62000.smt_ok);
         umax_heuristic_ok = (uu___845_62000.umax_heuristic_ok);
         tcenv = (uu___845_62000.tcenv);
         wl_implicits = (uu___845_62000.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____62014 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62014 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____62048 = FStar_Syntax_Util.type_u ()  in
            match uu____62048 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____62060 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____62060 with
                 | (uu____62078,tt,wl1) ->
                     let uu____62081 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____62081, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_62087  ->
    match uu___599_62087 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _62093  -> FStar_TypeChecker_Common.TProb _62093) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _62099  -> FStar_TypeChecker_Common.CProb _62099) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____62107 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____62107 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____62127  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____62169 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____62169 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____62169 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____62169 FStar_TypeChecker_Common.problem *
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
                        let uu____62256 =
                          let uu____62265 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62265]  in
                        FStar_List.append scope uu____62256
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____62308 =
                      let uu____62311 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____62311  in
                    FStar_List.append uu____62308
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____62330 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62330 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____62356 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62356;
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
                  (let uu____62430 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62430 with
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
                  (let uu____62518 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62518 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____62556 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62556 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____62556 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____62556 FStar_TypeChecker_Common.problem *
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
                          let uu____62624 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62624]  in
                        let uu____62643 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____62643
                     in
                  let uu____62646 =
                    let uu____62653 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_62664 = wl  in
                       {
                         attempting = (uu___928_62664.attempting);
                         wl_deferred = (uu___928_62664.wl_deferred);
                         ctr = (uu___928_62664.ctr);
                         defer_ok = (uu___928_62664.defer_ok);
                         smt_ok = (uu___928_62664.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_62664.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_62664.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____62653
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62646 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____62682 =
                              let uu____62687 =
                                let uu____62688 =
                                  let uu____62697 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____62697
                                   in
                                [uu____62688]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____62687
                               in
                            uu____62682 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____62725 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62725;
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
                let uu____62773 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____62773;
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
  'Auu____62788 .
    worklist ->
      'Auu____62788 FStar_TypeChecker_Common.problem ->
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
              let uu____62821 =
                let uu____62824 =
                  let uu____62825 =
                    let uu____62832 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____62832)  in
                  FStar_Syntax_Syntax.NT uu____62825  in
                [uu____62824]  in
              FStar_Syntax_Subst.subst uu____62821 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____62856 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____62856
        then
          let uu____62864 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____62867 = prob_to_string env d  in
          let uu____62869 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____62864 uu____62867 uu____62869 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____62885 -> failwith "impossible"  in
           let uu____62888 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____62904 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62906 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62904, uu____62906)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____62913 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62915 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62913, uu____62915)
              in
           match uu____62888 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_62943  ->
            match uu___600_62943 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____62955 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____62959 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____62959 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_62990  ->
           match uu___601_62990 with
           | UNIV uu____62993 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____63000 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____63000
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
        (fun uu___602_63028  ->
           match uu___602_63028 with
           | UNIV (u',t) ->
               let uu____63033 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____63033
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____63040 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63052 =
        let uu____63053 =
          let uu____63054 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____63054
           in
        FStar_Syntax_Subst.compress uu____63053  in
      FStar_All.pipe_right uu____63052 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63066 =
        let uu____63067 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____63067  in
      FStar_All.pipe_right uu____63066 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____63075 = FStar_Syntax_Util.head_and_args t  in
    match uu____63075 with
    | (h,uu____63094) ->
        let uu____63119 =
          let uu____63120 = FStar_Syntax_Subst.compress h  in
          uu____63120.FStar_Syntax_Syntax.n  in
        (match uu____63119 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____63125 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63138 = should_strongly_reduce t  in
      if uu____63138
      then
        let uu____63141 =
          let uu____63142 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____63142  in
        FStar_All.pipe_right uu____63141 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____63152 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____63152) ->
        (FStar_Syntax_Syntax.term * 'Auu____63152)
  =
  fun env  ->
    fun t  ->
      let uu____63175 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____63175, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____63227  ->
              match uu____63227 with
              | (x,imp) ->
                  let uu____63246 =
                    let uu___1025_63247 = x  in
                    let uu____63248 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_63247.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_63247.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____63248
                    }  in
                  (uu____63246, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____63272 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____63272
        | FStar_Syntax_Syntax.U_max us ->
            let uu____63276 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____63276
        | uu____63279 -> u2  in
      let uu____63280 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____63280
  
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
                (let uu____63401 = norm_refinement env t12  in
                 match uu____63401 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____63416;
                     FStar_Syntax_Syntax.vars = uu____63417;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____63441 =
                       let uu____63443 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____63445 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____63443 uu____63445
                        in
                     failwith uu____63441)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____63461 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____63461
          | FStar_Syntax_Syntax.Tm_uinst uu____63462 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63499 =
                   let uu____63500 = FStar_Syntax_Subst.compress t1'  in
                   uu____63500.FStar_Syntax_Syntax.n  in
                 match uu____63499 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63515 -> aux true t1'
                 | uu____63523 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____63538 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63569 =
                   let uu____63570 = FStar_Syntax_Subst.compress t1'  in
                   uu____63570.FStar_Syntax_Syntax.n  in
                 match uu____63569 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63585 -> aux true t1'
                 | uu____63593 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____63608 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63655 =
                   let uu____63656 = FStar_Syntax_Subst.compress t1'  in
                   uu____63656.FStar_Syntax_Syntax.n  in
                 match uu____63655 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63671 -> aux true t1'
                 | uu____63679 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____63694 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____63709 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____63724 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____63739 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____63754 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____63783 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____63816 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____63837 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____63864 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____63892 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____63929 ->
              let uu____63936 =
                let uu____63938 = FStar_Syntax_Print.term_to_string t12  in
                let uu____63940 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____63938 uu____63940
                 in
              failwith uu____63936
          | FStar_Syntax_Syntax.Tm_ascribed uu____63955 ->
              let uu____63982 =
                let uu____63984 = FStar_Syntax_Print.term_to_string t12  in
                let uu____63986 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____63984 uu____63986
                 in
              failwith uu____63982
          | FStar_Syntax_Syntax.Tm_delayed uu____64001 ->
              let uu____64024 =
                let uu____64026 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64028 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64026 uu____64028
                 in
              failwith uu____64024
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____64043 =
                let uu____64045 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64047 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64045 uu____64047
                 in
              failwith uu____64043
           in
        let uu____64062 = whnf env t1  in aux false uu____64062
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
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
      let uu____64123 = base_and_refinement env t  in
      FStar_All.pipe_right uu____64123 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____64164 = FStar_Syntax_Syntax.null_bv t  in
    (uu____64164, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____64191 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____64191 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____64251  ->
    match uu____64251 with
    | (t_base,refopt) ->
        let uu____64282 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____64282 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____64324 =
      let uu____64328 =
        let uu____64331 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____64358  ->
                  match uu____64358 with | (uu____64367,uu____64368,x) -> x))
           in
        FStar_List.append wl.attempting uu____64331  in
      FStar_List.map (wl_prob_to_string wl) uu____64328  in
    FStar_All.pipe_right uu____64324 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____64391 .
    ('Auu____64391 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____64403  ->
    match uu____64403 with
    | (uu____64410,c,args) ->
        let uu____64413 = print_ctx_uvar c  in
        let uu____64415 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____64413 uu____64415
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____64425 = FStar_Syntax_Util.head_and_args t  in
    match uu____64425 with
    | (head1,_args) ->
        let uu____64469 =
          let uu____64470 = FStar_Syntax_Subst.compress head1  in
          uu____64470.FStar_Syntax_Syntax.n  in
        (match uu____64469 with
         | FStar_Syntax_Syntax.Tm_uvar uu____64474 -> true
         | uu____64488 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____64496 = FStar_Syntax_Util.head_and_args t  in
    match uu____64496 with
    | (head1,_args) ->
        let uu____64539 =
          let uu____64540 = FStar_Syntax_Subst.compress head1  in
          uu____64540.FStar_Syntax_Syntax.n  in
        (match uu____64539 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____64544) -> u
         | uu____64561 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____64586 = FStar_Syntax_Util.head_and_args t  in
      match uu____64586 with
      | (head1,args) ->
          let uu____64633 =
            let uu____64634 = FStar_Syntax_Subst.compress head1  in
            uu____64634.FStar_Syntax_Syntax.n  in
          (match uu____64633 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____64642)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____64675 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_64700  ->
                         match uu___603_64700 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____64705 =
                               let uu____64706 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____64706.FStar_Syntax_Syntax.n  in
                             (match uu____64705 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____64711 -> false)
                         | uu____64713 -> true))
                  in
               (match uu____64675 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____64738 =
                        FStar_List.collect
                          (fun uu___604_64750  ->
                             match uu___604_64750 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____64754 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____64754]
                             | uu____64755 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____64738 FStar_List.rev  in
                    let uu____64778 =
                      let uu____64785 =
                        let uu____64794 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_64816  ->
                                  match uu___605_64816 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____64820 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____64820]
                                  | uu____64821 -> []))
                           in
                        FStar_All.pipe_right uu____64794 FStar_List.rev  in
                      let uu____64844 =
                        let uu____64847 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____64847  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____64785 uu____64844
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____64778 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____64883  ->
                                match uu____64883 with
                                | (x,i) ->
                                    let uu____64902 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____64902, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____64933  ->
                                match uu____64933 with
                                | (a,i) ->
                                    let uu____64952 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____64952, i)) args_sol
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
           | uu____64974 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____64996 =
          let uu____65019 =
            let uu____65020 = FStar_Syntax_Subst.compress k  in
            uu____65020.FStar_Syntax_Syntax.n  in
          match uu____65019 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____65102 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____65102)
              else
                (let uu____65137 = FStar_Syntax_Util.abs_formals t  in
                 match uu____65137 with
                 | (ys',t1,uu____65170) ->
                     let uu____65175 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____65175))
          | uu____65214 ->
              let uu____65215 =
                let uu____65220 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____65220)  in
              ((ys, t), uu____65215)
           in
        match uu____64996 with
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
                 let uu____65315 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____65315 c  in
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
               (let uu____65393 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____65393
                then
                  let uu____65398 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____65400 = print_ctx_uvar uv  in
                  let uu____65402 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____65398 uu____65400 uu____65402
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____65411 =
                   let uu____65413 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____65413  in
                 let uu____65416 =
                   let uu____65419 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____65419
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____65411 uu____65416 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____65452 =
               let uu____65453 =
                 let uu____65455 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____65457 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____65455 uu____65457
                  in
               failwith uu____65453  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____65523  ->
                       match uu____65523 with
                       | (a,i) ->
                           let uu____65544 =
                             let uu____65545 = FStar_Syntax_Subst.compress a
                                in
                             uu____65545.FStar_Syntax_Syntax.n  in
                           (match uu____65544 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____65571 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____65581 =
                 let uu____65583 = is_flex g  in
                 Prims.op_Negation uu____65583  in
               if uu____65581
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____65592 = destruct_flex_t g wl  in
                  match uu____65592 with
                  | ((uu____65597,uv1,args),wl1) ->
                      ((let uu____65602 = args_as_binders args  in
                        assign_solution uu____65602 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_65604 = wl1  in
              {
                attempting = (uu___1277_65604.attempting);
                wl_deferred = (uu___1277_65604.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_65604.defer_ok);
                smt_ok = (uu___1277_65604.smt_ok);
                umax_heuristic_ok = (uu___1277_65604.umax_heuristic_ok);
                tcenv = (uu___1277_65604.tcenv);
                wl_implicits = (uu___1277_65604.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____65629 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____65629
         then
           let uu____65634 = FStar_Util.string_of_int pid  in
           let uu____65636 =
             let uu____65638 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____65638 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____65634
             uu____65636
         else ());
        commit sol;
        (let uu___1285_65652 = wl  in
         {
           attempting = (uu___1285_65652.attempting);
           wl_deferred = (uu___1285_65652.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_65652.defer_ok);
           smt_ok = (uu___1285_65652.smt_ok);
           umax_heuristic_ok = (uu___1285_65652.umax_heuristic_ok);
           tcenv = (uu___1285_65652.tcenv);
           wl_implicits = (uu___1285_65652.wl_implicits)
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
             | (uu____65718,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____65746 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____65746
              in
           (let uu____65752 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____65752
            then
              let uu____65757 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____65761 =
                let uu____65763 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____65763 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____65757
                uu____65761
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____65798 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____65798 FStar_Util.set_elements  in
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
      let uu____65838 = occurs uk t  in
      match uu____65838 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____65877 =
                 let uu____65879 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____65881 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____65879 uu____65881
                  in
               FStar_Pervasives_Native.Some uu____65877)
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
            let uu____66001 = maximal_prefix bs_tail bs'_tail  in
            (match uu____66001 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____66052 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____66109  ->
             match uu____66109 with
             | (x,uu____66121) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____66139 = FStar_List.last bs  in
      match uu____66139 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____66163) ->
          let uu____66174 =
            FStar_Util.prefix_until
              (fun uu___606_66189  ->
                 match uu___606_66189 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____66192 -> false) g
             in
          (match uu____66174 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____66206,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____66243 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____66243 with
        | (pfx,uu____66253) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____66265 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____66265 with
             | (uu____66273,src',wl1) ->
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
                 | uu____66387 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____66388 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____66452  ->
                  fun uu____66453  ->
                    match (uu____66452, uu____66453) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____66556 =
                          let uu____66558 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____66558
                           in
                        if uu____66556
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____66592 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____66592
                           then
                             let uu____66609 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____66609)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____66388 with | (isect,uu____66659) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____66695 'Auu____66696 .
    (FStar_Syntax_Syntax.bv * 'Auu____66695) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____66696) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____66754  ->
              fun uu____66755  ->
                match (uu____66754, uu____66755) with
                | ((a,uu____66774),(b,uu____66776)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____66792 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____66792) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____66823  ->
           match uu____66823 with
           | (y,uu____66830) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____66840 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____66840) Prims.list ->
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
                   let uu____67002 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____67002
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____67035 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____67087 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____67131 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____67152 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_67160  ->
    match uu___607_67160 with
    | MisMatch (d1,d2) ->
        let uu____67172 =
          let uu____67174 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____67176 =
            let uu____67178 =
              let uu____67180 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____67180 ")"  in
            Prims.op_Hat ") (" uu____67178  in
          Prims.op_Hat uu____67174 uu____67176  in
        Prims.op_Hat "MisMatch (" uu____67172
    | HeadMatch u ->
        let uu____67187 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____67187
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_67196  ->
    match uu___608_67196 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____67213 -> HeadMatch false
  
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
          let uu____67235 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____67235 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____67246 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____67270 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____67280 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____67307 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____67307
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____67308 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____67309 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____67310 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____67323 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____67337 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____67361) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____67367,uu____67368) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____67410) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____67435;
             FStar_Syntax_Syntax.index = uu____67436;
             FStar_Syntax_Syntax.sort = t2;_},uu____67438)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____67446 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____67447 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____67448 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____67463 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____67470 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____67490 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____67490
  
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
           { FStar_Syntax_Syntax.blob = uu____67509;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67510;
             FStar_Syntax_Syntax.ltyp = uu____67511;
             FStar_Syntax_Syntax.rng = uu____67512;_},uu____67513)
            ->
            let uu____67524 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____67524 t21
        | (uu____67525,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____67526;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67527;
             FStar_Syntax_Syntax.ltyp = uu____67528;
             FStar_Syntax_Syntax.rng = uu____67529;_})
            ->
            let uu____67540 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____67540
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____67552 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____67552
            then FullMatch
            else
              (let uu____67557 =
                 let uu____67566 =
                   let uu____67569 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____67569  in
                 let uu____67570 =
                   let uu____67573 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____67573  in
                 (uu____67566, uu____67570)  in
               MisMatch uu____67557)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____67579),FStar_Syntax_Syntax.Tm_uinst (g,uu____67581)) ->
            let uu____67590 = head_matches env f g  in
            FStar_All.pipe_right uu____67590 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____67591) -> HeadMatch true
        | (uu____67593,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____67597 = FStar_Const.eq_const c d  in
            if uu____67597
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____67607),FStar_Syntax_Syntax.Tm_uvar (uv',uu____67609)) ->
            let uu____67642 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____67642
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____67652),FStar_Syntax_Syntax.Tm_refine (y,uu____67654)) ->
            let uu____67663 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67663 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____67665),uu____67666) ->
            let uu____67671 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____67671 head_match
        | (uu____67672,FStar_Syntax_Syntax.Tm_refine (x,uu____67674)) ->
            let uu____67679 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67679 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____67680,FStar_Syntax_Syntax.Tm_type uu____67681) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____67683,FStar_Syntax_Syntax.Tm_arrow uu____67684) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____67715),FStar_Syntax_Syntax.Tm_app
           (head',uu____67717)) ->
            let uu____67766 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____67766 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____67768),uu____67769) ->
            let uu____67794 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____67794 head_match
        | (uu____67795,FStar_Syntax_Syntax.Tm_app (head1,uu____67797)) ->
            let uu____67822 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____67822 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____67823,FStar_Syntax_Syntax.Tm_let
           uu____67824) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____67852,FStar_Syntax_Syntax.Tm_match uu____67853) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____67899,FStar_Syntax_Syntax.Tm_abs
           uu____67900) -> HeadMatch true
        | uu____67938 ->
            let uu____67943 =
              let uu____67952 = delta_depth_of_term env t11  in
              let uu____67955 = delta_depth_of_term env t21  in
              (uu____67952, uu____67955)  in
            MisMatch uu____67943
  
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
            let head1 = FStar_Syntax_Util.head_of t  in
            (let uu____68021 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68021
             then
               let uu____68026 = FStar_Syntax_Print.term_to_string t  in
               let uu____68028 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____68026 uu____68028
             else ());
            (let uu____68033 =
               let uu____68034 = FStar_Syntax_Util.un_uinst head1  in
               uu____68034.FStar_Syntax_Syntax.n  in
             match uu____68033 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68040 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____68040 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____68054 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____68054
                        then
                          let uu____68059 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____68059
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____68064 ->
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
                      let uu____68081 =
                        let uu____68083 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____68083 = FStar_Syntax_Util.Equal  in
                      if uu____68081
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____68090 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____68090
                          then
                            let uu____68095 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____68097 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____68095 uu____68097
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____68102 -> FStar_Pervasives_Native.None)
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
            (let uu____68254 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68254
             then
               let uu____68259 = FStar_Syntax_Print.term_to_string t11  in
               let uu____68261 = FStar_Syntax_Print.term_to_string t21  in
               let uu____68263 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____68259
                 uu____68261 uu____68263
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____68291 =
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
               match uu____68291 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____68339 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____68339 with
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
                  uu____68377),uu____68378)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68399 =
                      let uu____68408 = maybe_inline t11  in
                      let uu____68411 = maybe_inline t21  in
                      (uu____68408, uu____68411)  in
                    match uu____68399 with
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
                 (uu____68454,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____68455))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68476 =
                      let uu____68485 = maybe_inline t11  in
                      let uu____68488 = maybe_inline t21  in
                      (uu____68485, uu____68488)  in
                    match uu____68476 with
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
             | MisMatch uu____68543 -> fail1 n_delta r t11 t21
             | uu____68552 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____68567 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____68567
           then
             let uu____68572 = FStar_Syntax_Print.term_to_string t1  in
             let uu____68574 = FStar_Syntax_Print.term_to_string t2  in
             let uu____68576 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____68584 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____68601 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____68601
                    (fun uu____68636  ->
                       match uu____68636 with
                       | (t11,t21) ->
                           let uu____68644 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____68646 =
                             let uu____68648 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____68648  in
                           Prims.op_Hat uu____68644 uu____68646))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____68572 uu____68574 uu____68576 uu____68584
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____68665 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____68665 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_68680  ->
    match uu___609_68680 with
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
      let uu___1789_68729 = p  in
      let uu____68732 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____68733 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_68729.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____68732;
        FStar_TypeChecker_Common.relation =
          (uu___1789_68729.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____68733;
        FStar_TypeChecker_Common.element =
          (uu___1789_68729.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_68729.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_68729.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_68729.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_68729.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_68729.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____68748 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____68748
            (fun _68753  -> FStar_TypeChecker_Common.TProb _68753)
      | FStar_TypeChecker_Common.CProb uu____68754 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____68777 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____68777 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____68785 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____68785 with
           | (lh,lhs_args) ->
               let uu____68832 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____68832 with
                | (rh,rhs_args) ->
                    let uu____68879 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____68892,FStar_Syntax_Syntax.Tm_uvar uu____68893)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____68982 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69009,uu____69010)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____69025,FStar_Syntax_Syntax.Tm_uvar uu____69026)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69041,FStar_Syntax_Syntax.Tm_arrow
                         uu____69042) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69072 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69072.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69072.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69072.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69072.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69072.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69072.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69072.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69072.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69072.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69075,FStar_Syntax_Syntax.Tm_type uu____69076)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69092 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69092.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69092.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69092.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69092.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69092.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69092.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69092.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69092.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69092.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____69095,FStar_Syntax_Syntax.Tm_uvar uu____69096)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69112 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69112.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69112.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69112.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69112.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69112.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69112.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69112.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69112.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69112.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____69115,FStar_Syntax_Syntax.Tm_uvar uu____69116)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69131,uu____69132)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____69147,FStar_Syntax_Syntax.Tm_uvar uu____69148)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____69163,uu____69164) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____68879 with
                     | (rank,tp1) ->
                         let uu____69177 =
                           FStar_All.pipe_right
                             (let uu___1860_69181 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_69181.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_69181.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_69181.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_69181.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_69181.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_69181.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_69181.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_69181.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_69181.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _69184  ->
                                FStar_TypeChecker_Common.TProb _69184)
                            in
                         (rank, uu____69177))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____69188 =
            FStar_All.pipe_right
              (let uu___1864_69192 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_69192.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_69192.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_69192.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_69192.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_69192.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_69192.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_69192.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_69192.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_69192.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _69195  -> FStar_TypeChecker_Common.CProb _69195)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____69188)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____69255 probs =
      match uu____69255 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____69336 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____69357 = rank wl.tcenv hd1  in
               (match uu____69357 with
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
                      (let uu____69418 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____69423 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____69423)
                          in
                       if uu____69418
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
          let uu____69496 = FStar_Syntax_Util.head_and_args t  in
          match uu____69496 with
          | (hd1,uu____69515) ->
              let uu____69540 =
                let uu____69541 = FStar_Syntax_Subst.compress hd1  in
                uu____69541.FStar_Syntax_Syntax.n  in
              (match uu____69540 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____69546) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____69581  ->
                           match uu____69581 with
                           | (y,uu____69590) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____69613  ->
                                       match uu____69613 with
                                       | (x,uu____69622) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____69627 -> false)
           in
        let uu____69629 = rank tcenv p  in
        match uu____69629 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____69638 -> true
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
    match projectee with | UDeferred _0 -> true | uu____69675 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____69694 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____69714 -> false
  
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
                        let uu____69776 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____69776 with
                        | (k,uu____69784) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____69797 -> false)))
            | uu____69799 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____69851 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____69859 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____69859 = (Prims.parse_int "0")))
                           in
                        if uu____69851 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____69880 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____69888 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____69888 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____69880)
               in
            let uu____69892 = filter1 u12  in
            let uu____69895 = filter1 u22  in (uu____69892, uu____69895)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____69930 = filter_out_common_univs us1 us2  in
                   (match uu____69930 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____69990 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____69990 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____69993 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____70004 =
                             let uu____70006 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____70008 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____70006 uu____70008
                              in
                           UFailed uu____70004))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70034 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70034 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70060 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70060 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____70063 ->
                   let uu____70068 =
                     let uu____70070 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____70072 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____70070 uu____70072 msg
                      in
                   UFailed uu____70068)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____70075,uu____70076) ->
              let uu____70078 =
                let uu____70080 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70082 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70080 uu____70082
                 in
              failwith uu____70078
          | (FStar_Syntax_Syntax.U_unknown ,uu____70085) ->
              let uu____70086 =
                let uu____70088 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70090 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70088 uu____70090
                 in
              failwith uu____70086
          | (uu____70093,FStar_Syntax_Syntax.U_bvar uu____70094) ->
              let uu____70096 =
                let uu____70098 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70100 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70098 uu____70100
                 in
              failwith uu____70096
          | (uu____70103,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____70104 =
                let uu____70106 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70108 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70106 uu____70108
                 in
              failwith uu____70104
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____70138 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____70138
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____70155 = occurs_univ v1 u3  in
              if uu____70155
              then
                let uu____70158 =
                  let uu____70160 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70162 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70160 uu____70162
                   in
                try_umax_components u11 u21 uu____70158
              else
                (let uu____70167 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70167)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____70179 = occurs_univ v1 u3  in
              if uu____70179
              then
                let uu____70182 =
                  let uu____70184 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70186 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70184 uu____70186
                   in
                try_umax_components u11 u21 uu____70182
              else
                (let uu____70191 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70191)
          | (FStar_Syntax_Syntax.U_max uu____70192,uu____70193) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70201 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70201
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____70207,FStar_Syntax_Syntax.U_max uu____70208) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70216 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70216
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____70222,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____70224,FStar_Syntax_Syntax.U_name uu____70225) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____70227) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____70229) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70231,FStar_Syntax_Syntax.U_succ uu____70232) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70234,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
  
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
      let uu____70341 = bc1  in
      match uu____70341 with
      | (bs1,mk_cod1) ->
          let uu____70385 = bc2  in
          (match uu____70385 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____70496 = aux xs ys  in
                     (match uu____70496 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____70579 =
                       let uu____70586 = mk_cod1 xs  in ([], uu____70586)  in
                     let uu____70589 =
                       let uu____70596 = mk_cod2 ys  in ([], uu____70596)  in
                     (uu____70579, uu____70589)
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
                  let uu____70665 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____70665 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____70668 =
                    let uu____70669 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____70669 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____70668
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____70674 = has_type_guard t1 t2  in (uu____70674, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____70675 = has_type_guard t2 t1  in (uu____70675, wl)
  
let is_flex_pat :
  'Auu____70685 'Auu____70686 'Auu____70687 .
    ('Auu____70685 * 'Auu____70686 * 'Auu____70687 Prims.list) -> Prims.bool
  =
  fun uu___610_70701  ->
    match uu___610_70701 with
    | (uu____70710,uu____70711,[]) -> true
    | uu____70715 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____70748 = f  in
      match uu____70748 with
      | (uu____70755,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____70756;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____70757;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____70760;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____70761;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____70762;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____70763;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____70833  ->
                 match uu____70833 with
                 | (y,uu____70842) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____70996 =
                  let uu____71011 =
                    let uu____71014 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71014  in
                  ((FStar_List.rev pat_binders), uu____71011)  in
                FStar_Pervasives_Native.Some uu____70996
            | (uu____71047,[]) ->
                let uu____71078 =
                  let uu____71093 =
                    let uu____71096 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71096  in
                  ((FStar_List.rev pat_binders), uu____71093)  in
                FStar_Pervasives_Native.Some uu____71078
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____71187 =
                  let uu____71188 = FStar_Syntax_Subst.compress a  in
                  uu____71188.FStar_Syntax_Syntax.n  in
                (match uu____71187 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____71208 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____71208
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_71238 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_71238.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_71238.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____71242 =
                            let uu____71243 =
                              let uu____71250 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____71250)  in
                            FStar_Syntax_Syntax.NT uu____71243  in
                          [uu____71242]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_71266 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_71266.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_71266.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____71267 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____71307 =
                  let uu____71322 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____71322  in
                (match uu____71307 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____71397 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____71430 ->
               let uu____71431 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____71431 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____71753 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____71753
       then
         let uu____71758 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____71758
       else ());
      (let uu____71763 = next_prob probs  in
       match uu____71763 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_71790 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_71790.wl_deferred);
               ctr = (uu___2219_71790.ctr);
               defer_ok = (uu___2219_71790.defer_ok);
               smt_ok = (uu___2219_71790.smt_ok);
               umax_heuristic_ok = (uu___2219_71790.umax_heuristic_ok);
               tcenv = (uu___2219_71790.tcenv);
               wl_implicits = (uu___2219_71790.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____71799 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____71799
                 then
                   let uu____71802 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____71802
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
                       solve env
                         (defer "deferring flex_rigid or flex_flex subtyping"
                            hd1 probs1)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___2231_71814 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_71814.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_71814.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_71814.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_71814.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_71814.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_71814.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_71814.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_71814.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_71814.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____71840 ->
                let uu____71851 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____71922  ->
                          match uu____71922 with
                          | (c,uu____71933,uu____71934) -> c < probs.ctr))
                   in
                (match uu____71851 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____71989 =
                            let uu____71994 =
                              FStar_List.map
                                (fun uu____72012  ->
                                   match uu____72012 with
                                   | (uu____72026,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____71994, (probs.wl_implicits))  in
                          Success uu____71989
                      | uu____72034 ->
                          let uu____72045 =
                            let uu___2249_72046 = probs  in
                            let uu____72047 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____72070  ->
                                      match uu____72070 with
                                      | (uu____72079,uu____72080,y) -> y))
                               in
                            {
                              attempting = uu____72047;
                              wl_deferred = rest;
                              ctr = (uu___2249_72046.ctr);
                              defer_ok = (uu___2249_72046.defer_ok);
                              smt_ok = (uu___2249_72046.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_72046.umax_heuristic_ok);
                              tcenv = (uu___2249_72046.tcenv);
                              wl_implicits = (uu___2249_72046.wl_implicits)
                            }  in
                          solve env uu____72045))))

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
            let uu____72091 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____72091 with
            | USolved wl1 ->
                let uu____72093 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____72093
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
                  let uu____72147 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____72147 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____72150 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____72163;
                  FStar_Syntax_Syntax.vars = uu____72164;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____72167;
                  FStar_Syntax_Syntax.vars = uu____72168;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____72181,uu____72182) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____72190,FStar_Syntax_Syntax.Tm_uinst uu____72191) ->
                failwith "Impossible: expect head symbols to match"
            | uu____72199 -> USolved wl

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
            ((let uu____72211 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____72211
              then
                let uu____72216 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____72216 msg
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
               let uu____72308 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____72308 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____72363 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____72363
                then
                  let uu____72368 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____72370 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____72368 uu____72370
                else ());
               (let uu____72375 = head_matches_delta env1 wl2 t1 t2  in
                match uu____72375 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____72421 = eq_prob t1 t2 wl2  in
                         (match uu____72421 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____72442 ->
                         let uu____72451 = eq_prob t1 t2 wl2  in
                         (match uu____72451 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____72501 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____72516 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____72517 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____72516, uu____72517)
                           | FStar_Pervasives_Native.None  ->
                               let uu____72522 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____72523 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____72522, uu____72523)
                            in
                         (match uu____72501 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____72554 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____72554 with
                                | (t1_hd,t1_args) ->
                                    let uu____72599 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____72599 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____72665 =
                                              let uu____72672 =
                                                let uu____72683 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____72683 :: t1_args  in
                                              let uu____72700 =
                                                let uu____72709 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____72709 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____72758  ->
                                                   fun uu____72759  ->
                                                     fun uu____72760  ->
                                                       match (uu____72758,
                                                               uu____72759,
                                                               uu____72760)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____72810),
                                                          (a2,uu____72812))
                                                           ->
                                                           let uu____72849 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____72849
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____72672
                                                uu____72700
                                               in
                                            match uu____72665 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_72875 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_72875.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_72875.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_72875.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____72887 =
                                                  solve env1 wl'  in
                                                (match uu____72887 with
                                                 | Success (uu____72890,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_72894
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_72894.attempting);
                                                            wl_deferred =
                                                              (uu___2412_72894.wl_deferred);
                                                            ctr =
                                                              (uu___2412_72894.ctr);
                                                            defer_ok =
                                                              (uu___2412_72894.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_72894.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_72894.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_72894.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____72895 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____72928 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____72928 with
                                | (t1_base,p1_opt) ->
                                    let uu____72964 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____72964 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____73063 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____73063
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
                                               let uu____73116 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____73116
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
                                               let uu____73148 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73148
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
                                               let uu____73180 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73180
                                           | uu____73183 -> t_base  in
                                         let uu____73200 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____73200 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____73214 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____73214, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____73221 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____73221 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____73257 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____73257 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____73293 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____73293
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
                              let uu____73317 = combine t11 t21 wl2  in
                              (match uu____73317 with
                               | (t12,ps,wl3) ->
                                   ((let uu____73350 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____73350
                                     then
                                       let uu____73355 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____73355
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____73397 ts1 =
               match uu____73397 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____73460 = pairwise out t wl2  in
                        (match uu____73460 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____73496 =
               let uu____73507 = FStar_List.hd ts  in (uu____73507, [], wl1)
                in
             let uu____73516 = FStar_List.tl ts  in
             aux uu____73496 uu____73516  in
           let uu____73523 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____73523 with
           | (this_flex,this_rigid) ->
               let uu____73549 =
                 let uu____73550 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____73550.FStar_Syntax_Syntax.n  in
               (match uu____73549 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____73575 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____73575
                    then
                      let uu____73578 = destruct_flex_t this_flex wl  in
                      (match uu____73578 with
                       | (flex,wl1) ->
                           let uu____73585 = quasi_pattern env flex  in
                           (match uu____73585 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____73604 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____73604
                                  then
                                    let uu____73609 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____73609
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____73616 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_73619 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_73619.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_73619.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_73619.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_73619.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_73619.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_73619.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_73619.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_73619.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_73619.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____73616)
                | uu____73620 ->
                    ((let uu____73622 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____73622
                      then
                        let uu____73627 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____73627
                      else ());
                     (let uu____73632 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____73632 with
                      | (u,_args) ->
                          let uu____73675 =
                            let uu____73676 = FStar_Syntax_Subst.compress u
                               in
                            uu____73676.FStar_Syntax_Syntax.n  in
                          (match uu____73675 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____73704 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____73704 with
                                 | (u',uu____73723) ->
                                     let uu____73748 =
                                       let uu____73749 = whnf env u'  in
                                       uu____73749.FStar_Syntax_Syntax.n  in
                                     (match uu____73748 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____73771 -> false)
                                  in
                               let uu____73773 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_73796  ->
                                         match uu___611_73796 with
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
                                              | uu____73810 -> false)
                                         | uu____73814 -> false))
                                  in
                               (match uu____73773 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____73829 = whnf env this_rigid
                                         in
                                      let uu____73830 =
                                        FStar_List.collect
                                          (fun uu___612_73836  ->
                                             match uu___612_73836 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____73842 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____73842]
                                             | uu____73846 -> [])
                                          bounds_probs
                                         in
                                      uu____73829 :: uu____73830  in
                                    let uu____73847 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____73847 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____73880 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____73895 =
                                               let uu____73896 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____73896.FStar_Syntax_Syntax.n
                                                in
                                             match uu____73895 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____73908 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____73908)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____73919 -> bound  in
                                           let uu____73920 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____73920)  in
                                         (match uu____73880 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____73955 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____73955
                                                then
                                                  let wl'1 =
                                                    let uu___2574_73961 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_73961.wl_deferred);
                                                      ctr =
                                                        (uu___2574_73961.ctr);
                                                      defer_ok =
                                                        (uu___2574_73961.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_73961.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_73961.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_73961.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_73961.wl_implicits)
                                                    }  in
                                                  let uu____73962 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____73962
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____73968 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_73970 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_73970.wl_deferred);
                                                       ctr =
                                                         (uu___2579_73970.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_73970.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_73970.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_73970.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____73968 with
                                                | Success (uu____73972,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_73975 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_73975.wl_deferred);
                                                        ctr =
                                                          (uu___2585_73975.ctr);
                                                        defer_ok =
                                                          (uu___2585_73975.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_73975.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_73975.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_73975.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_73975.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_73977 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_73977.attempting);
                                                        wl_deferred =
                                                          (uu___2588_73977.wl_deferred);
                                                        ctr =
                                                          (uu___2588_73977.ctr);
                                                        defer_ok =
                                                          (uu___2588_73977.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_73977.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_73977.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_73977.tcenv);
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
                                                    let uu____73993 =
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
                                                    ((let uu____74007 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____74007
                                                      then
                                                        let uu____74012 =
                                                          let uu____74014 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____74014
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____74012
                                                      else ());
                                                     (let uu____74027 =
                                                        let uu____74042 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____74042)
                                                         in
                                                      match uu____74027 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____74064))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74090 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74090
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
                                                                  let uu____74110
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74110))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74135 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74135
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
                                                                    let uu____74155
                                                                    =
                                                                    let uu____74160
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____74160
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____74155
                                                                    [] wl2
                                                                     in
                                                                  let uu____74166
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74166))))
                                                      | uu____74167 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____74183 when flip ->
                               let uu____74184 =
                                 let uu____74186 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74188 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____74186 uu____74188
                                  in
                               failwith uu____74184
                           | uu____74191 ->
                               let uu____74192 =
                                 let uu____74194 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74196 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____74194 uu____74196
                                  in
                               failwith uu____74192)))))

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
                      (fun uu____74232  ->
                         match uu____74232 with
                         | (x,i) ->
                             let uu____74251 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____74251, i)) bs_lhs
                     in
                  let uu____74254 = lhs  in
                  match uu____74254 with
                  | (uu____74255,u_lhs,uu____74257) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____74354 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____74364 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____74364, univ)
                             in
                          match uu____74354 with
                          | (k,univ) ->
                              let uu____74371 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____74371 with
                               | (uu____74388,u,wl3) ->
                                   let uu____74391 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____74391, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____74417 =
                              let uu____74430 =
                                let uu____74441 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____74441 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____74492  ->
                                   fun uu____74493  ->
                                     match (uu____74492, uu____74493) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____74594 =
                                           let uu____74601 =
                                             let uu____74604 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____74604
                                              in
                                           copy_uvar u_lhs [] uu____74601 wl2
                                            in
                                         (match uu____74594 with
                                          | (uu____74633,t_a,wl3) ->
                                              let uu____74636 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____74636 with
                                               | (uu____74655,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____74430
                                ([], wl1)
                               in
                            (match uu____74417 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_74711 = ct  in
                                   let uu____74712 =
                                     let uu____74715 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____74715
                                      in
                                   let uu____74730 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_74711.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_74711.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____74712;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____74730;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_74711.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_74748 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_74748.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_74748.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____74751 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____74751 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____74813 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____74813 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____74824 =
                                          let uu____74829 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____74829)  in
                                        TERM uu____74824  in
                                      let uu____74830 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____74830 with
                                       | (sub_prob,wl3) ->
                                           let uu____74844 =
                                             let uu____74845 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____74845
                                              in
                                           solve env uu____74844))
                             | (x,imp)::formals2 ->
                                 let uu____74867 =
                                   let uu____74874 =
                                     let uu____74877 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____74877
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____74874 wl1
                                    in
                                 (match uu____74867 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____74898 =
                                          let uu____74901 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____74901
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____74898 u_x
                                         in
                                      let uu____74902 =
                                        let uu____74905 =
                                          let uu____74908 =
                                            let uu____74909 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____74909, imp)  in
                                          [uu____74908]  in
                                        FStar_List.append bs_terms
                                          uu____74905
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____74902 formals2 wl2)
                              in
                           let uu____74936 = occurs_check u_lhs arrow1  in
                           (match uu____74936 with
                            | (uu____74949,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____74965 =
                                    let uu____74967 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____74967
                                     in
                                  giveup_or_defer env orig wl uu____74965
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
              (let uu____75000 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____75000
               then
                 let uu____75005 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____75008 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____75005 (rel_to_string (p_rel orig)) uu____75008
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____75135 = rhs wl1 scope env1 subst1  in
                     (match uu____75135 with
                      | (rhs_prob,wl2) ->
                          ((let uu____75156 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____75156
                            then
                              let uu____75161 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____75161
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____75239 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____75239 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_75241 = hd1  in
                       let uu____75242 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_75241.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_75241.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75242
                       }  in
                     let hd21 =
                       let uu___2773_75246 = hd2  in
                       let uu____75247 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_75246.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_75246.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75247
                       }  in
                     let uu____75250 =
                       let uu____75255 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____75255
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____75250 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____75276 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____75276
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____75283 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____75283 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____75350 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____75350
                                  in
                               ((let uu____75368 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____75368
                                 then
                                   let uu____75373 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____75375 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____75373
                                     uu____75375
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____75408 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____75444 = aux wl [] env [] bs1 bs2  in
               match uu____75444 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____75499 = attempt sub_probs wl2  in
                   solve env uu____75499)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist ->
             (FStar_TypeChecker_Common.prob * Prims.string) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2808_75520 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_75520.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_75520.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____75533 = try_solve env wl'  in
          match uu____75533 with
          | Success (uu____75534,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_75538 = wl  in
                  {
                    attempting = (uu___2817_75538.attempting);
                    wl_deferred = (uu___2817_75538.wl_deferred);
                    ctr = (uu___2817_75538.ctr);
                    defer_ok = (uu___2817_75538.defer_ok);
                    smt_ok = (uu___2817_75538.smt_ok);
                    umax_heuristic_ok = (uu___2817_75538.umax_heuristic_ok);
                    tcenv = (uu___2817_75538.tcenv);
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
        (let uu____75550 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____75550 wl)

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
              let uu____75564 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____75564 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____75598 = lhs1  in
              match uu____75598 with
              | (uu____75601,ctx_u,uu____75603) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____75611 ->
                        let uu____75612 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____75612 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____75661 = quasi_pattern env1 lhs1  in
              match uu____75661 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____75695) ->
                  let uu____75700 = lhs1  in
                  (match uu____75700 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____75715 = occurs_check ctx_u rhs1  in
                       (match uu____75715 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____75766 =
                                let uu____75774 =
                                  let uu____75776 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____75776
                                   in
                                FStar_Util.Inl uu____75774  in
                              (uu____75766, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____75804 =
                                 let uu____75806 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____75806  in
                               if uu____75804
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____75833 =
                                    let uu____75841 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____75841  in
                                  let uu____75847 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____75833, uu____75847)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____75891 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____75891 with
              | (rhs_hd,args) ->
                  let uu____75934 = FStar_Util.prefix args  in
                  (match uu____75934 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____76006 = lhs1  in
                       (match uu____76006 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____76010 =
                              let uu____76021 =
                                let uu____76028 =
                                  let uu____76031 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____76031
                                   in
                                copy_uvar u_lhs [] uu____76028 wl1  in
                              match uu____76021 with
                              | (uu____76058,t_last_arg,wl2) ->
                                  let uu____76061 =
                                    let uu____76068 =
                                      let uu____76069 =
                                        let uu____76078 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____76078]  in
                                      FStar_List.append bs_lhs uu____76069
                                       in
                                    copy_uvar u_lhs uu____76068 t_res_lhs wl2
                                     in
                                  (match uu____76061 with
                                   | (uu____76113,lhs',wl3) ->
                                       let uu____76116 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____76116 with
                                        | (uu____76133,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____76010 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____76154 =
                                     let uu____76155 =
                                       let uu____76160 =
                                         let uu____76161 =
                                           let uu____76164 =
                                             let uu____76169 =
                                               let uu____76170 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____76170]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____76169
                                              in
                                           uu____76164
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____76161
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____76160)  in
                                     TERM uu____76155  in
                                   [uu____76154]  in
                                 let uu____76195 =
                                   let uu____76202 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____76202 with
                                   | (p1,wl3) ->
                                       let uu____76222 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____76222 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____76195 with
                                  | (sub_probs,wl3) ->
                                      let uu____76254 =
                                        let uu____76255 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____76255  in
                                      solve env1 uu____76254))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____76289 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____76289 with
                | (uu____76307,args) ->
                    (match args with | [] -> false | uu____76343 -> true)
                 in
              let is_arrow rhs2 =
                let uu____76362 =
                  let uu____76363 = FStar_Syntax_Subst.compress rhs2  in
                  uu____76363.FStar_Syntax_Syntax.n  in
                match uu____76362 with
                | FStar_Syntax_Syntax.Tm_arrow uu____76367 -> true
                | uu____76383 -> false  in
              let uu____76385 = quasi_pattern env1 lhs1  in
              match uu____76385 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76396 =
                    let uu____76398 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____76398
                     in
                  giveup_or_defer env1 orig1 wl1 uu____76396
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____76407 = is_app rhs1  in
                  if uu____76407
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____76412 = is_arrow rhs1  in
                     if uu____76412
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____76417 =
                          let uu____76419 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____76419
                           in
                        giveup_or_defer env1 orig1 wl1 uu____76417))
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
                let uu____76430 = lhs  in
                (match uu____76430 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____76434 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____76434 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____76452 =
                              let uu____76456 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____76456
                               in
                            FStar_All.pipe_right uu____76452
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____76477 = occurs_check ctx_uv rhs1  in
                          (match uu____76477 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____76506 =
                                   let uu____76508 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____76508
                                    in
                                 giveup_or_defer env orig wl uu____76506
                               else
                                 (let uu____76514 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____76514
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____76521 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____76521
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____76525 =
                                         let uu____76527 =
                                           names_to_string1 fvs2  in
                                         let uu____76529 =
                                           names_to_string1 fvs1  in
                                         let uu____76531 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____76527 uu____76529
                                           uu____76531
                                          in
                                       giveup_or_defer env orig wl
                                         uu____76525)
                                    else first_order orig env wl lhs rhs1))
                      | uu____76543 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____76550 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____76550 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____76576 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____76576
                             | (FStar_Util.Inl msg,uu____76578) ->
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
                  (let uu____76623 =
                     let uu____76640 = quasi_pattern env lhs  in
                     let uu____76647 = quasi_pattern env rhs  in
                     (uu____76640, uu____76647)  in
                   match uu____76623 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____76690 = lhs  in
                       (match uu____76690 with
                        | ({ FStar_Syntax_Syntax.n = uu____76691;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____76693;_},u_lhs,uu____76695)
                            ->
                            let uu____76698 = rhs  in
                            (match uu____76698 with
                             | (uu____76699,u_rhs,uu____76701) ->
                                 let uu____76702 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____76702
                                 then
                                   let uu____76709 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____76709
                                 else
                                   (let uu____76712 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____76712 with
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
                                        let uu____76744 =
                                          let uu____76751 =
                                            let uu____76754 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____76754
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____76751
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____76744 with
                                         | (uu____76766,w,wl1) ->
                                             let w_app =
                                               let uu____76772 =
                                                 let uu____76777 =
                                                   FStar_List.map
                                                     (fun uu____76788  ->
                                                        match uu____76788
                                                        with
                                                        | (z,uu____76796) ->
                                                            let uu____76801 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____76801) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____76777
                                                  in
                                               uu____76772
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____76803 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____76803
                                               then
                                                 let uu____76808 =
                                                   let uu____76812 =
                                                     flex_t_to_string lhs  in
                                                   let uu____76814 =
                                                     let uu____76818 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____76820 =
                                                       let uu____76824 =
                                                         term_to_string w  in
                                                       let uu____76826 =
                                                         let uu____76830 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____76839 =
                                                           let uu____76843 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____76852 =
                                                             let uu____76856
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____76856]
                                                              in
                                                           uu____76843 ::
                                                             uu____76852
                                                            in
                                                         uu____76830 ::
                                                           uu____76839
                                                          in
                                                       uu____76824 ::
                                                         uu____76826
                                                        in
                                                     uu____76818 ::
                                                       uu____76820
                                                      in
                                                   uu____76812 :: uu____76814
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____76808
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____76873 =
                                                     let uu____76878 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____76878)  in
                                                   TERM uu____76873  in
                                                 let uu____76879 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____76879
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____76887 =
                                                        let uu____76892 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____76892)
                                                         in
                                                      TERM uu____76887  in
                                                    [s1; s2])
                                                  in
                                               let uu____76893 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____76893))))))
                   | uu____76894 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____76965 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____76965
            then
              let uu____76970 = FStar_Syntax_Print.term_to_string t1  in
              let uu____76972 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____76974 = FStar_Syntax_Print.term_to_string t2  in
              let uu____76976 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____76970 uu____76972 uu____76974 uu____76976
            else ());
           (let uu____76987 = FStar_Syntax_Util.head_and_args t1  in
            match uu____76987 with
            | (head1,args1) ->
                let uu____77030 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____77030 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____77100 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____77100 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____77126 =
                         let uu____77128 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____77130 = args_to_string args1  in
                         let uu____77134 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____77136 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____77128 uu____77130 uu____77134 uu____77136
                          in
                       giveup env1 uu____77126 orig
                     else
                       (let uu____77143 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____77148 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____77148 = FStar_Syntax_Util.Equal)
                           in
                        if uu____77143
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_77152 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_77152.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_77152.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_77152.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_77152.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_77152.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_77152.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_77152.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_77152.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____77162 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____77162
                                    else solve env1 wl2))
                        else
                          (let uu____77167 = base_and_refinement env1 t1  in
                           match uu____77167 with
                           | (base1,refinement1) ->
                               let uu____77192 = base_and_refinement env1 t2
                                  in
                               (match uu____77192 with
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
                                           let uu____77357 =
                                             FStar_List.fold_right
                                               (fun uu____77397  ->
                                                  fun uu____77398  ->
                                                    match (uu____77397,
                                                            uu____77398)
                                                    with
                                                    | (((a1,uu____77450),
                                                        (a2,uu____77452)),
                                                       (probs,wl3)) ->
                                                        let uu____77501 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____77501
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____77357 with
                                           | (subprobs,wl3) ->
                                               ((let uu____77544 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77544
                                                 then
                                                   let uu____77549 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____77549
                                                 else ());
                                                (let uu____77555 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____77555
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
                                                    (let uu____77582 =
                                                       mk_sub_probs wl3  in
                                                     match uu____77582 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____77598 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____77598
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____77606 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____77606))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____77630 =
                                                    mk_sub_probs wl3  in
                                                  match uu____77630 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____77644 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____77644)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____77670 =
                                           match uu____77670 with
                                           | (prob,reason) ->
                                               ((let uu____77681 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77681
                                                 then
                                                   let uu____77686 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____77688 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____77686 uu____77688
                                                     reason
                                                 else ());
                                                (let uu____77693 =
                                                   let uu____77702 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____77705 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____77702, uu____77705)
                                                    in
                                                 match uu____77693 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____77718 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____77718 with
                                                      | (head1',uu____77736)
                                                          ->
                                                          let uu____77761 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____77761
                                                           with
                                                           | (head2',uu____77779)
                                                               ->
                                                               let uu____77804
                                                                 =
                                                                 let uu____77809
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____77810
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____77809,
                                                                   uu____77810)
                                                                  in
                                                               (match uu____77804
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____77812
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77812
                                                                    then
                                                                    let uu____77817
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____77819
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____77821
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____77823
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____77817
                                                                    uu____77819
                                                                    uu____77821
                                                                    uu____77823
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____77828
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_77836
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_77836.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_77836.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_77836.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_77836.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_77836.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_77836.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_77836.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_77836.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____77838
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77838
                                                                    then
                                                                    let uu____77843
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____77843
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____77848 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____77860 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____77860 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____77868 =
                                             let uu____77869 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____77869.FStar_Syntax_Syntax.n
                                              in
                                           match uu____77868 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____77874 -> false  in
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
                                          | uu____77877 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____77880 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_77916 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_77916.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_77916.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_77916.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_77916.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_77916.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_77916.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_77916.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_77916.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____77992 = destruct_flex_t scrutinee wl1  in
             match uu____77992 with
             | ((_t,uv,_args),wl2) ->
                 let uu____78003 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____78003 with
                  | (xs,pat_term,uu____78019,uu____78020) ->
                      let uu____78025 =
                        FStar_List.fold_left
                          (fun uu____78048  ->
                             fun x  ->
                               match uu____78048 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____78069 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____78069 with
                                    | (uu____78088,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____78025 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____78109 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____78109 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_78126 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_78126.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_78126.umax_heuristic_ok);
                                    tcenv = (uu___3212_78126.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____78138 = solve env1 wl'  in
                                (match uu____78138 with
                                 | Success (uu____78141,imps) ->
                                     let wl'1 =
                                       let uu___3220_78144 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_78144.wl_deferred);
                                         ctr = (uu___3220_78144.ctr);
                                         defer_ok =
                                           (uu___3220_78144.defer_ok);
                                         smt_ok = (uu___3220_78144.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_78144.umax_heuristic_ok);
                                         tcenv = (uu___3220_78144.tcenv);
                                         wl_implicits =
                                           (uu___3220_78144.wl_implicits)
                                       }  in
                                     let uu____78145 = solve env1 wl'1  in
                                     (match uu____78145 with
                                      | Success (uu____78148,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_78152 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_78152.attempting);
                                                 wl_deferred =
                                                   (uu___3228_78152.wl_deferred);
                                                 ctr = (uu___3228_78152.ctr);
                                                 defer_ok =
                                                   (uu___3228_78152.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_78152.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_78152.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_78152.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____78153 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____78160 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____78183 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____78183
                 then
                   let uu____78188 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____78190 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____78188 uu____78190
                 else ());
                (let uu____78195 =
                   let uu____78216 =
                     let uu____78225 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____78225)  in
                   let uu____78232 =
                     let uu____78241 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____78241)  in
                   (uu____78216, uu____78232)  in
                 match uu____78195 with
                 | ((uu____78271,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____78274;
                                   FStar_Syntax_Syntax.vars = uu____78275;_}),
                    (s,t)) ->
                     let uu____78346 =
                       let uu____78348 = is_flex scrutinee  in
                       Prims.op_Negation uu____78348  in
                     if uu____78346
                     then
                       ((let uu____78359 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____78359
                         then
                           let uu____78364 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____78364
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____78383 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78383
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____78398 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78398
                           then
                             let uu____78403 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____78405 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____78403 uu____78405
                           else ());
                          (let pat_discriminates uu___613_78430 =
                             match uu___613_78430 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____78446;
                                  FStar_Syntax_Syntax.p = uu____78447;_},FStar_Pervasives_Native.None
                                ,uu____78448) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____78462;
                                  FStar_Syntax_Syntax.p = uu____78463;_},FStar_Pervasives_Native.None
                                ,uu____78464) -> true
                             | uu____78491 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____78594 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____78594 with
                                       | (uu____78596,uu____78597,t') ->
                                           let uu____78615 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____78615 with
                                            | (FullMatch ,uu____78627) ->
                                                true
                                            | (HeadMatch
                                               uu____78641,uu____78642) ->
                                                true
                                            | uu____78657 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____78694 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____78694
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____78705 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____78705 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____78793,uu____78794) ->
                                       branches1
                                   | uu____78939 -> branches  in
                                 let uu____78994 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79003 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79003 with
                                        | (p,uu____79007,uu____79008) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79037  -> FStar_Util.Inr _79037)
                                   uu____78994))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79067 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79067 with
                                | (p,uu____79076,e) ->
                                    ((let uu____79095 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79095
                                      then
                                        let uu____79100 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79102 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79100 uu____79102
                                      else ());
                                     (let uu____79107 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79122  -> FStar_Util.Inr _79122)
                                        uu____79107)))))
                 | ((s,t),(uu____79125,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____79128;
                                         FStar_Syntax_Syntax.vars =
                                           uu____79129;_}))
                     ->
                     let uu____79198 =
                       let uu____79200 = is_flex scrutinee  in
                       Prims.op_Negation uu____79200  in
                     if uu____79198
                     then
                       ((let uu____79211 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____79211
                         then
                           let uu____79216 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____79216
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____79235 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79235
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____79250 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79250
                           then
                             let uu____79255 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____79257 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____79255 uu____79257
                           else ());
                          (let pat_discriminates uu___613_79282 =
                             match uu___613_79282 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____79298;
                                  FStar_Syntax_Syntax.p = uu____79299;_},FStar_Pervasives_Native.None
                                ,uu____79300) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____79314;
                                  FStar_Syntax_Syntax.p = uu____79315;_},FStar_Pervasives_Native.None
                                ,uu____79316) -> true
                             | uu____79343 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____79446 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____79446 with
                                       | (uu____79448,uu____79449,t') ->
                                           let uu____79467 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____79467 with
                                            | (FullMatch ,uu____79479) ->
                                                true
                                            | (HeadMatch
                                               uu____79493,uu____79494) ->
                                                true
                                            | uu____79509 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____79546 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____79546
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____79557 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____79557 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____79645,uu____79646) ->
                                       branches1
                                   | uu____79791 -> branches  in
                                 let uu____79846 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79855 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79855 with
                                        | (p,uu____79859,uu____79860) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79889  -> FStar_Util.Inr _79889)
                                   uu____79846))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79919 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79919 with
                                | (p,uu____79928,e) ->
                                    ((let uu____79947 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79947
                                      then
                                        let uu____79952 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79954 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79952 uu____79954
                                      else ());
                                     (let uu____79959 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79974  -> FStar_Util.Inr _79974)
                                        uu____79959)))))
                 | uu____79975 ->
                     ((let uu____79997 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____79997
                       then
                         let uu____80002 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____80004 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____80002 uu____80004
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____80050 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____80050
            then
              let uu____80055 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____80057 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____80059 = FStar_Syntax_Print.term_to_string t1  in
              let uu____80061 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____80055 uu____80057 uu____80059 uu____80061
            else ());
           (let uu____80066 = head_matches_delta env1 wl1 t1 t2  in
            match uu____80066 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____80097,uu____80098) ->
                     let rec may_relate head3 =
                       let uu____80126 =
                         let uu____80127 = FStar_Syntax_Subst.compress head3
                            in
                         uu____80127.FStar_Syntax_Syntax.n  in
                       match uu____80126 with
                       | FStar_Syntax_Syntax.Tm_name uu____80131 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____80133 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____80158 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____80158 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____80160 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____80163
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____80164 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____80167,uu____80168) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____80210) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____80216) ->
                           may_relate t
                       | uu____80221 -> false  in
                     let uu____80223 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____80223 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____80244 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____80244
                          then
                            let uu____80247 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____80247 with
                             | (guard,wl2) ->
                                 let uu____80254 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____80254)
                          else
                            (let uu____80257 =
                               let uu____80259 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____80261 =
                                 let uu____80263 =
                                   let uu____80267 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____80267
                                     (fun x  ->
                                        let uu____80274 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80274)
                                    in
                                 FStar_Util.dflt "" uu____80263  in
                               let uu____80279 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____80281 =
                                 let uu____80283 =
                                   let uu____80287 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____80287
                                     (fun x  ->
                                        let uu____80294 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80294)
                                    in
                                 FStar_Util.dflt "" uu____80283  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____80259 uu____80261 uu____80279
                                 uu____80281
                                in
                             giveup env1 uu____80257 orig))
                 | (HeadMatch (true ),uu____80300) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____80315 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____80315 with
                        | (guard,wl2) ->
                            let uu____80322 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____80322)
                     else
                       (let uu____80325 =
                          let uu____80327 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____80329 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____80327 uu____80329
                           in
                        giveup env1 uu____80325 orig)
                 | (uu____80332,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_80346 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_80346.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_80346.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_80346.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_80346.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_80346.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_80346.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_80346.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_80346.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____80373 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____80373
          then
            let uu____80376 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____80376
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____80382 =
                let uu____80385 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80385  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____80382 t1);
             (let uu____80404 =
                let uu____80407 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80407  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____80404 t2);
             (let uu____80426 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____80426
              then
                let uu____80430 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____80432 =
                  let uu____80434 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____80436 =
                    let uu____80438 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____80438  in
                  Prims.op_Hat uu____80434 uu____80436  in
                let uu____80441 =
                  let uu____80443 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____80445 =
                    let uu____80447 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____80447  in
                  Prims.op_Hat uu____80443 uu____80445  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____80430 uu____80432 uu____80441
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____80454,uu____80455) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____80479,FStar_Syntax_Syntax.Tm_delayed uu____80480) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____80504,uu____80505) ->
                  let uu____80532 =
                    let uu___3432_80533 = problem  in
                    let uu____80534 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_80533.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80534;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_80533.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_80533.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_80533.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_80533.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_80533.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_80533.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_80533.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_80533.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80532 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____80535,uu____80536) ->
                  let uu____80543 =
                    let uu___3438_80544 = problem  in
                    let uu____80545 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_80544.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80545;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_80544.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_80544.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_80544.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_80544.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_80544.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_80544.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_80544.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_80544.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80543 wl
              | (uu____80546,FStar_Syntax_Syntax.Tm_ascribed uu____80547) ->
                  let uu____80574 =
                    let uu___3444_80575 = problem  in
                    let uu____80576 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_80575.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_80575.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_80575.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80576;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_80575.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_80575.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_80575.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_80575.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_80575.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_80575.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80574 wl
              | (uu____80577,FStar_Syntax_Syntax.Tm_meta uu____80578) ->
                  let uu____80585 =
                    let uu___3450_80586 = problem  in
                    let uu____80587 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_80586.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_80586.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_80586.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80587;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_80586.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_80586.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_80586.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_80586.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_80586.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_80586.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80585 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____80589),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____80591)) ->
                  let uu____80600 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____80600
              | (FStar_Syntax_Syntax.Tm_bvar uu____80601,uu____80602) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____80604,FStar_Syntax_Syntax.Tm_bvar uu____80605) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_80675 =
                    match uu___614_80675 with
                    | [] -> c
                    | bs ->
                        let uu____80703 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____80703
                     in
                  let uu____80714 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____80714 with
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
                                    let uu____80863 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____80863
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
                  let mk_t t l uu___615_80952 =
                    match uu___615_80952 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____80994 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____80994 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____81139 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____81140 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____81139
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____81140 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____81142,uu____81143) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81174 -> true
                    | uu____81194 -> false  in
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
                      (let uu____81254 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81262 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81262.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81262.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81262.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81262.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81262.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81262.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81262.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81262.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81262.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81262.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81262.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81262.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81262.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81262.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81262.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81262.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81262.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81262.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81262.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81262.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81262.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81262.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81262.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81262.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81262.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81262.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81262.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81262.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81262.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81262.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81262.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81262.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81262.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81262.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81262.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81262.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81262.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81262.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81262.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81262.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81254 with
                       | (uu____81267,ty,uu____81269) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81278 =
                                 let uu____81279 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81279.FStar_Syntax_Syntax.n  in
                               match uu____81278 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81282 ->
                                   let uu____81289 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81289
                               | uu____81290 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81293 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81293
                             then
                               let uu____81298 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81300 =
                                 let uu____81302 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81302
                                  in
                               let uu____81303 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81298 uu____81300 uu____81303
                             else ());
                            r1))
                     in
                  let uu____81308 =
                    let uu____81325 = maybe_eta t1  in
                    let uu____81332 = maybe_eta t2  in
                    (uu____81325, uu____81332)  in
                  (match uu____81308 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81374 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81374.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81374.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81374.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81374.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81374.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81374.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81374.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81374.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81395 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81395
                       then
                         let uu____81398 = destruct_flex_t not_abs wl  in
                         (match uu____81398 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81415 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81415.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81415.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81415.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81415.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81415.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81415.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81415.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81415.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81439 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81439
                       then
                         let uu____81442 = destruct_flex_t not_abs wl  in
                         (match uu____81442 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81459 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81459.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81459.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81459.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81459.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81459.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81459.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81459.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81459.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81463 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____81481,FStar_Syntax_Syntax.Tm_abs uu____81482) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81513 -> true
                    | uu____81533 -> false  in
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
                      (let uu____81593 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81601 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81601.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81601.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81601.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81601.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81601.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81601.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81601.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81601.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81601.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81601.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81601.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81601.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81601.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81601.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81601.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81601.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81601.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81601.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81601.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81601.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81601.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81601.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81601.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81601.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81601.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81601.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81601.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81601.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81601.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81601.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81601.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81601.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81601.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81601.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81601.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81601.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81601.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81601.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81601.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81601.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81593 with
                       | (uu____81606,ty,uu____81608) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81617 =
                                 let uu____81618 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81618.FStar_Syntax_Syntax.n  in
                               match uu____81617 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81621 ->
                                   let uu____81628 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81628
                               | uu____81629 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81632 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81632
                             then
                               let uu____81637 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81639 =
                                 let uu____81641 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81641
                                  in
                               let uu____81642 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81637 uu____81639 uu____81642
                             else ());
                            r1))
                     in
                  let uu____81647 =
                    let uu____81664 = maybe_eta t1  in
                    let uu____81671 = maybe_eta t2  in
                    (uu____81664, uu____81671)  in
                  (match uu____81647 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81713 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81713.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81713.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81713.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81713.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81713.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81713.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81713.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81713.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81734 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81734
                       then
                         let uu____81737 = destruct_flex_t not_abs wl  in
                         (match uu____81737 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81754 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81754.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81754.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81754.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81754.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81754.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81754.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81754.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81754.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81778 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81778
                       then
                         let uu____81781 = destruct_flex_t not_abs wl  in
                         (match uu____81781 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81798 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81798.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81798.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81798.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81798.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81798.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81798.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81798.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81798.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81802 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____81832 =
                    let uu____81837 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____81837 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_81865 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81865.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81865.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81867 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81867.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81867.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____81868,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_81883 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81883.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81883.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81885 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81885.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81885.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____81886 -> (x1, x2)  in
                  (match uu____81832 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____81905 = as_refinement false env t11  in
                       (match uu____81905 with
                        | (x12,phi11) ->
                            let uu____81913 = as_refinement false env t21  in
                            (match uu____81913 with
                             | (x22,phi21) ->
                                 ((let uu____81922 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____81922
                                   then
                                     ((let uu____81927 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____81929 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81931 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____81927
                                         uu____81929 uu____81931);
                                      (let uu____81934 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____81936 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81938 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____81934
                                         uu____81936 uu____81938))
                                   else ());
                                  (let uu____81943 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____81943 with
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
                                         let uu____82014 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____82014
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____82026 =
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
                                         (let uu____82039 =
                                            let uu____82042 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82042
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____82039
                                            (p_guard base_prob));
                                         (let uu____82061 =
                                            let uu____82064 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82064
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____82061
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____82083 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____82083)
                                          in
                                       let has_uvars =
                                         (let uu____82088 =
                                            let uu____82090 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____82090
                                             in
                                          Prims.op_Negation uu____82088) ||
                                           (let uu____82094 =
                                              let uu____82096 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____82096
                                               in
                                            Prims.op_Negation uu____82094)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____82100 =
                                           let uu____82105 =
                                             let uu____82114 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____82114]  in
                                           mk_t_problem wl1 uu____82105 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____82100 with
                                          | (ref_prob,wl2) ->
                                              let uu____82136 =
                                                solve env1
                                                  (let uu___3657_82138 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_82138.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_82138.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_82138.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_82138.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_82138.wl_implicits)
                                                   })
                                                 in
                                              (match uu____82136 with
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
                                               | Success uu____82155 ->
                                                   let guard =
                                                     let uu____82163 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____82163
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_82172 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_82172.attempting);
                                                       wl_deferred =
                                                         (uu___3668_82172.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_82172.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_82172.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_82172.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_82172.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_82172.wl_implicits)
                                                     }  in
                                                   let uu____82174 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____82174))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82177,FStar_Syntax_Syntax.Tm_uvar uu____82178) ->
                  let uu____82203 = destruct_flex_t t1 wl  in
                  (match uu____82203 with
                   | (f1,wl1) ->
                       let uu____82210 = destruct_flex_t t2 wl1  in
                       (match uu____82210 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82217;
                    FStar_Syntax_Syntax.pos = uu____82218;
                    FStar_Syntax_Syntax.vars = uu____82219;_},uu____82220),FStar_Syntax_Syntax.Tm_uvar
                 uu____82221) ->
                  let uu____82270 = destruct_flex_t t1 wl  in
                  (match uu____82270 with
                   | (f1,wl1) ->
                       let uu____82277 = destruct_flex_t t2 wl1  in
                       (match uu____82277 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82284,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82285;
                    FStar_Syntax_Syntax.pos = uu____82286;
                    FStar_Syntax_Syntax.vars = uu____82287;_},uu____82288))
                  ->
                  let uu____82337 = destruct_flex_t t1 wl  in
                  (match uu____82337 with
                   | (f1,wl1) ->
                       let uu____82344 = destruct_flex_t t2 wl1  in
                       (match uu____82344 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82351;
                    FStar_Syntax_Syntax.pos = uu____82352;
                    FStar_Syntax_Syntax.vars = uu____82353;_},uu____82354),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82355;
                    FStar_Syntax_Syntax.pos = uu____82356;
                    FStar_Syntax_Syntax.vars = uu____82357;_},uu____82358))
                  ->
                  let uu____82431 = destruct_flex_t t1 wl  in
                  (match uu____82431 with
                   | (f1,wl1) ->
                       let uu____82438 = destruct_flex_t t2 wl1  in
                       (match uu____82438 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____82445,uu____82446) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82459 = destruct_flex_t t1 wl  in
                  (match uu____82459 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82466;
                    FStar_Syntax_Syntax.pos = uu____82467;
                    FStar_Syntax_Syntax.vars = uu____82468;_},uu____82469),uu____82470)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82507 = destruct_flex_t t1 wl  in
                  (match uu____82507 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____82514,FStar_Syntax_Syntax.Tm_uvar uu____82515) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____82528,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82529;
                    FStar_Syntax_Syntax.pos = uu____82530;
                    FStar_Syntax_Syntax.vars = uu____82531;_},uu____82532))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82569,FStar_Syntax_Syntax.Tm_arrow uu____82570) ->
                  solve_t' env
                    (let uu___3768_82598 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82598.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82598.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82598.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82598.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82598.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82598.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82598.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82598.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82598.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82599;
                    FStar_Syntax_Syntax.pos = uu____82600;
                    FStar_Syntax_Syntax.vars = uu____82601;_},uu____82602),FStar_Syntax_Syntax.Tm_arrow
                 uu____82603) ->
                  solve_t' env
                    (let uu___3768_82655 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82655.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82655.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82655.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82655.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82655.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82655.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82655.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82655.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82655.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82656,FStar_Syntax_Syntax.Tm_uvar uu____82657) ->
                  let uu____82670 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82670
              | (uu____82671,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82672;
                    FStar_Syntax_Syntax.pos = uu____82673;
                    FStar_Syntax_Syntax.vars = uu____82674;_},uu____82675))
                  ->
                  let uu____82712 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82712
              | (FStar_Syntax_Syntax.Tm_uvar uu____82713,uu____82714) ->
                  let uu____82727 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82727
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82728;
                    FStar_Syntax_Syntax.pos = uu____82729;
                    FStar_Syntax_Syntax.vars = uu____82730;_},uu____82731),uu____82732)
                  ->
                  let uu____82769 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82769
              | (FStar_Syntax_Syntax.Tm_refine uu____82770,uu____82771) ->
                  let t21 =
                    let uu____82779 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____82779  in
                  solve_t env
                    (let uu___3803_82805 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_82805.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_82805.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_82805.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_82805.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_82805.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_82805.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_82805.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_82805.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_82805.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82806,FStar_Syntax_Syntax.Tm_refine uu____82807) ->
                  let t11 =
                    let uu____82815 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____82815  in
                  solve_t env
                    (let uu___3810_82841 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_82841.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_82841.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_82841.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_82841.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_82841.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_82841.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_82841.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_82841.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_82841.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____82923 =
                    let uu____82924 = guard_of_prob env wl problem t1 t2  in
                    match uu____82924 with
                    | (guard,wl1) ->
                        let uu____82931 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____82931
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____83150 = br1  in
                        (match uu____83150 with
                         | (p1,w1,uu____83179) ->
                             let uu____83196 = br2  in
                             (match uu____83196 with
                              | (p2,w2,uu____83219) ->
                                  let uu____83224 =
                                    let uu____83226 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____83226  in
                                  if uu____83224
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____83253 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____83253 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____83290 = br2  in
                                         (match uu____83290 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____83323 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____83323
                                                 in
                                              let uu____83328 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____83359,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____83380) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____83439 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____83439 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____83328
                                                (fun uu____83511  ->
                                                   match uu____83511 with
                                                   | (wprobs,wl2) ->
                                                       let uu____83548 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____83548
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____83569
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____83569
                                                              then
                                                                let uu____83574
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____83576
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____83574
                                                                  uu____83576
                                                              else ());
                                                             (let uu____83582
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____83582
                                                                (fun
                                                                   uu____83618
                                                                    ->
                                                                   match uu____83618
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
                    | uu____83747 -> FStar_Pervasives_Native.None  in
                  let uu____83788 = solve_branches wl brs1 brs2  in
                  (match uu____83788 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____83839 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____83839 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____83873 =
                                FStar_List.map
                                  (fun uu____83885  ->
                                     match uu____83885 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____83873  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____83894 =
                              let uu____83895 =
                                let uu____83896 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____83896
                                  (let uu___3909_83904 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_83904.attempting);
                                     wl_deferred =
                                       (uu___3909_83904.wl_deferred);
                                     ctr = (uu___3909_83904.ctr);
                                     defer_ok = (uu___3909_83904.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_83904.umax_heuristic_ok);
                                     tcenv = (uu___3909_83904.tcenv);
                                     wl_implicits =
                                       (uu___3909_83904.wl_implicits)
                                   })
                                 in
                              solve env uu____83895  in
                            (match uu____83894 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____83909 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____83916,uu____83917) ->
                  let head1 =
                    let uu____83941 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____83941
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____83987 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____83987
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84033 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84033
                    then
                      let uu____84037 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84039 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84041 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84037 uu____84039 uu____84041
                    else ());
                   (let no_free_uvars t =
                      (let uu____84055 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84055) &&
                        (let uu____84059 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84059)
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
                      let uu____84076 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84076 = FStar_Syntax_Util.Equal  in
                    let uu____84077 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84077
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84081 = equal t1 t2  in
                         (if uu____84081
                          then
                            let uu____84084 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84084
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84089 =
                            let uu____84096 = equal t1 t2  in
                            if uu____84096
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84109 = mk_eq2 wl env orig t1 t2  in
                               match uu____84109 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84089 with
                          | (guard,wl1) ->
                              let uu____84130 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84130))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____84133,uu____84134) ->
                  let head1 =
                    let uu____84142 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84142
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84188 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84188
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84234 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84234
                    then
                      let uu____84238 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84240 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84242 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84238 uu____84240 uu____84242
                    else ());
                   (let no_free_uvars t =
                      (let uu____84256 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84256) &&
                        (let uu____84260 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84260)
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
                      let uu____84277 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84277 = FStar_Syntax_Util.Equal  in
                    let uu____84278 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84278
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84282 = equal t1 t2  in
                         (if uu____84282
                          then
                            let uu____84285 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84285
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84290 =
                            let uu____84297 = equal t1 t2  in
                            if uu____84297
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84310 = mk_eq2 wl env orig t1 t2  in
                               match uu____84310 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84290 with
                          | (guard,wl1) ->
                              let uu____84331 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84331))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____84334,uu____84335) ->
                  let head1 =
                    let uu____84337 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84337
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84383 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84383
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84429 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84429
                    then
                      let uu____84433 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84435 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84437 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84433 uu____84435 uu____84437
                    else ());
                   (let no_free_uvars t =
                      (let uu____84451 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84451) &&
                        (let uu____84455 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84455)
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
                      let uu____84472 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84472 = FStar_Syntax_Util.Equal  in
                    let uu____84473 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84473
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84477 = equal t1 t2  in
                         (if uu____84477
                          then
                            let uu____84480 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84480
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84485 =
                            let uu____84492 = equal t1 t2  in
                            if uu____84492
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84505 = mk_eq2 wl env orig t1 t2  in
                               match uu____84505 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84485 with
                          | (guard,wl1) ->
                              let uu____84526 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84526))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____84529,uu____84530) ->
                  let head1 =
                    let uu____84532 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84532
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84578 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84578
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84624 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84624
                    then
                      let uu____84628 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84630 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84632 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84628 uu____84630 uu____84632
                    else ());
                   (let no_free_uvars t =
                      (let uu____84646 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84646) &&
                        (let uu____84650 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84650)
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
                      let uu____84667 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84667 = FStar_Syntax_Util.Equal  in
                    let uu____84668 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84668
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84672 = equal t1 t2  in
                         (if uu____84672
                          then
                            let uu____84675 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84675
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84680 =
                            let uu____84687 = equal t1 t2  in
                            if uu____84687
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84700 = mk_eq2 wl env orig t1 t2  in
                               match uu____84700 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84680 with
                          | (guard,wl1) ->
                              let uu____84721 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84721))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____84724,uu____84725) ->
                  let head1 =
                    let uu____84727 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84727
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84773 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84773
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84819 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84819
                    then
                      let uu____84823 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84825 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84827 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84823 uu____84825 uu____84827
                    else ());
                   (let no_free_uvars t =
                      (let uu____84841 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84841) &&
                        (let uu____84845 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84845)
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
                      let uu____84862 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84862 = FStar_Syntax_Util.Equal  in
                    let uu____84863 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84863
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84867 = equal t1 t2  in
                         (if uu____84867
                          then
                            let uu____84870 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84870
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84875 =
                            let uu____84882 = equal t1 t2  in
                            if uu____84882
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84895 = mk_eq2 wl env orig t1 t2  in
                               match uu____84895 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84875 with
                          | (guard,wl1) ->
                              let uu____84916 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84916))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____84919,uu____84920) ->
                  let head1 =
                    let uu____84938 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84938
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84984 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84984
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85030 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85030
                    then
                      let uu____85034 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85036 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85038 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85034 uu____85036 uu____85038
                    else ());
                   (let no_free_uvars t =
                      (let uu____85052 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85052) &&
                        (let uu____85056 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85056)
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
                      let uu____85073 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85073 = FStar_Syntax_Util.Equal  in
                    let uu____85074 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85074
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85078 = equal t1 t2  in
                         (if uu____85078
                          then
                            let uu____85081 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85081
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85086 =
                            let uu____85093 = equal t1 t2  in
                            if uu____85093
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85106 = mk_eq2 wl env orig t1 t2  in
                               match uu____85106 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85086 with
                          | (guard,wl1) ->
                              let uu____85127 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85127))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85130,FStar_Syntax_Syntax.Tm_match uu____85131) ->
                  let head1 =
                    let uu____85155 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85155
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85201 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85201
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85247 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85247
                    then
                      let uu____85251 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85253 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85255 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85251 uu____85253 uu____85255
                    else ());
                   (let no_free_uvars t =
                      (let uu____85269 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85269) &&
                        (let uu____85273 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85273)
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
                      let uu____85290 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85290 = FStar_Syntax_Util.Equal  in
                    let uu____85291 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85291
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85295 = equal t1 t2  in
                         (if uu____85295
                          then
                            let uu____85298 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85298
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85303 =
                            let uu____85310 = equal t1 t2  in
                            if uu____85310
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85323 = mk_eq2 wl env orig t1 t2  in
                               match uu____85323 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85303 with
                          | (guard,wl1) ->
                              let uu____85344 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85344))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85347,FStar_Syntax_Syntax.Tm_uinst uu____85348) ->
                  let head1 =
                    let uu____85356 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85356
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85396 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85396
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85436 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85436
                    then
                      let uu____85440 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85442 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85444 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85440 uu____85442 uu____85444
                    else ());
                   (let no_free_uvars t =
                      (let uu____85458 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85458) &&
                        (let uu____85462 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85462)
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
                      let uu____85479 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85479 = FStar_Syntax_Util.Equal  in
                    let uu____85480 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85480
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85484 = equal t1 t2  in
                         (if uu____85484
                          then
                            let uu____85487 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85487
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85492 =
                            let uu____85499 = equal t1 t2  in
                            if uu____85499
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85512 = mk_eq2 wl env orig t1 t2  in
                               match uu____85512 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85492 with
                          | (guard,wl1) ->
                              let uu____85533 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85533))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85536,FStar_Syntax_Syntax.Tm_name uu____85537) ->
                  let head1 =
                    let uu____85539 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85539
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85579 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85579
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85619 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85619
                    then
                      let uu____85623 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85625 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85627 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85623 uu____85625 uu____85627
                    else ());
                   (let no_free_uvars t =
                      (let uu____85641 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85641) &&
                        (let uu____85645 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85645)
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
                      let uu____85662 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85662 = FStar_Syntax_Util.Equal  in
                    let uu____85663 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85663
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85667 = equal t1 t2  in
                         (if uu____85667
                          then
                            let uu____85670 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85670
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85675 =
                            let uu____85682 = equal t1 t2  in
                            if uu____85682
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85695 = mk_eq2 wl env orig t1 t2  in
                               match uu____85695 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85675 with
                          | (guard,wl1) ->
                              let uu____85716 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85716))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85719,FStar_Syntax_Syntax.Tm_constant uu____85720) ->
                  let head1 =
                    let uu____85722 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85722
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85762 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85762
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85802 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85802
                    then
                      let uu____85806 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85808 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85810 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85806 uu____85808 uu____85810
                    else ());
                   (let no_free_uvars t =
                      (let uu____85824 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85824) &&
                        (let uu____85828 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85828)
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
                      let uu____85845 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85845 = FStar_Syntax_Util.Equal  in
                    let uu____85846 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85846
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85850 = equal t1 t2  in
                         (if uu____85850
                          then
                            let uu____85853 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85853
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85858 =
                            let uu____85865 = equal t1 t2  in
                            if uu____85865
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85878 = mk_eq2 wl env orig t1 t2  in
                               match uu____85878 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85858 with
                          | (guard,wl1) ->
                              let uu____85899 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85899))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85902,FStar_Syntax_Syntax.Tm_fvar uu____85903) ->
                  let head1 =
                    let uu____85905 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85905
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85945 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85945
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85985 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85985
                    then
                      let uu____85989 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85991 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85993 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85989 uu____85991 uu____85993
                    else ());
                   (let no_free_uvars t =
                      (let uu____86007 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86007) &&
                        (let uu____86011 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86011)
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
                      let uu____86028 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86028 = FStar_Syntax_Util.Equal  in
                    let uu____86029 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86029
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86033 = equal t1 t2  in
                         (if uu____86033
                          then
                            let uu____86036 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86036
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86041 =
                            let uu____86048 = equal t1 t2  in
                            if uu____86048
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86061 = mk_eq2 wl env orig t1 t2  in
                               match uu____86061 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86041 with
                          | (guard,wl1) ->
                              let uu____86082 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86082))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86085,FStar_Syntax_Syntax.Tm_app uu____86086) ->
                  let head1 =
                    let uu____86104 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86104
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86144 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86144
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86184 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86184
                    then
                      let uu____86188 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86190 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86192 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86188 uu____86190 uu____86192
                    else ());
                   (let no_free_uvars t =
                      (let uu____86206 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86206) &&
                        (let uu____86210 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86210)
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
                      let uu____86227 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86227 = FStar_Syntax_Util.Equal  in
                    let uu____86228 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86228
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86232 = equal t1 t2  in
                         (if uu____86232
                          then
                            let uu____86235 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86235
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86240 =
                            let uu____86247 = equal t1 t2  in
                            if uu____86247
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86260 = mk_eq2 wl env orig t1 t2  in
                               match uu____86260 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86240 with
                          | (guard,wl1) ->
                              let uu____86281 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86281))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____86284,FStar_Syntax_Syntax.Tm_let uu____86285) ->
                  let uu____86312 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____86312
                  then
                    let uu____86315 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____86315
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____86319,uu____86320) ->
                  let uu____86334 =
                    let uu____86340 =
                      let uu____86342 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____86344 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____86346 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____86348 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____86342 uu____86344 uu____86346 uu____86348
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____86340)
                     in
                  FStar_Errors.raise_error uu____86334
                    t1.FStar_Syntax_Syntax.pos
              | (uu____86352,FStar_Syntax_Syntax.Tm_let uu____86353) ->
                  let uu____86367 =
                    let uu____86373 =
                      let uu____86375 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____86377 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____86379 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____86381 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____86375 uu____86377 uu____86379 uu____86381
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____86373)
                     in
                  FStar_Errors.raise_error uu____86367
                    t1.FStar_Syntax_Syntax.pos
              | uu____86385 -> giveup env "head tag mismatch" orig))))

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
          (let uu____86449 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____86449
           then
             let uu____86454 =
               let uu____86456 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____86456  in
             let uu____86457 =
               let uu____86459 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____86459  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____86454 uu____86457
           else ());
          (let uu____86463 =
             let uu____86465 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____86465  in
           if uu____86463
           then
             let uu____86468 =
               let uu____86470 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____86472 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____86470 uu____86472
                in
             giveup env uu____86468 orig
           else
             (let uu____86477 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____86477 with
              | (ret_sub_prob,wl1) ->
                  let uu____86485 =
                    FStar_List.fold_right2
                      (fun uu____86522  ->
                         fun uu____86523  ->
                           fun uu____86524  ->
                             match (uu____86522, uu____86523, uu____86524)
                             with
                             | ((a1,uu____86568),(a2,uu____86570),(arg_sub_probs,wl2))
                                 ->
                                 let uu____86603 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____86603 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____86485 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____86633 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____86633  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____86641 = attempt sub_probs wl3  in
                       solve env uu____86641)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____86664 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____86667)::[] -> wp1
              | uu____86692 ->
                  let uu____86703 =
                    let uu____86705 =
                      let uu____86707 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____86707  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____86705
                     in
                  failwith uu____86703
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____86714 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____86714]
              | x -> x  in
            let uu____86716 =
              let uu____86727 =
                let uu____86736 =
                  let uu____86737 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____86737 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____86736  in
              [uu____86727]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____86716;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____86755 = lift_c1 ()  in solve_eq uu____86755 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_86764  ->
                       match uu___616_86764 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____86769 -> false))
                in
             let uu____86771 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____86801)::uu____86802,(wp2,uu____86804)::uu____86805)
                   -> (wp1, wp2)
               | uu____86878 ->
                   let uu____86903 =
                     let uu____86909 =
                       let uu____86911 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____86913 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____86911 uu____86913
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____86909)
                      in
                   FStar_Errors.raise_error uu____86903
                     env.FStar_TypeChecker_Env.range
                in
             match uu____86771 with
             | (wpc1,wpc2) ->
                 let uu____86923 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____86923
                 then
                   let uu____86928 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____86928 wl
                 else
                   (let uu____86932 =
                      let uu____86939 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____86939  in
                    match uu____86932 with
                    | (c2_decl,qualifiers) ->
                        let uu____86960 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____86960
                        then
                          let c1_repr =
                            let uu____86967 =
                              let uu____86968 =
                                let uu____86969 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____86969  in
                              let uu____86970 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____86968 uu____86970
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____86967
                             in
                          let c2_repr =
                            let uu____86972 =
                              let uu____86973 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____86974 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____86973 uu____86974
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____86972
                             in
                          let uu____86975 =
                            let uu____86980 =
                              let uu____86982 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____86984 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____86982 uu____86984
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____86980
                             in
                          (match uu____86975 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____86990 = attempt [prob] wl2  in
                               solve env uu____86990)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____87005 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____87005
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____87014 =
                                     let uu____87021 =
                                       let uu____87022 =
                                         let uu____87039 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____87042 =
                                           let uu____87053 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____87062 =
                                             let uu____87073 =
                                               let uu____87082 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____87082
                                                in
                                             [uu____87073]  in
                                           uu____87053 :: uu____87062  in
                                         (uu____87039, uu____87042)  in
                                       FStar_Syntax_Syntax.Tm_app uu____87022
                                        in
                                     FStar_Syntax_Syntax.mk uu____87021  in
                                   uu____87014 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____87131 =
                                    let uu____87138 =
                                      let uu____87139 =
                                        let uu____87156 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____87159 =
                                          let uu____87170 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____87179 =
                                            let uu____87190 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____87199 =
                                              let uu____87210 =
                                                let uu____87219 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____87219
                                                 in
                                              [uu____87210]  in
                                            uu____87190 :: uu____87199  in
                                          uu____87170 :: uu____87179  in
                                        (uu____87156, uu____87159)  in
                                      FStar_Syntax_Syntax.Tm_app uu____87139
                                       in
                                    FStar_Syntax_Syntax.mk uu____87138  in
                                  uu____87131 FStar_Pervasives_Native.None r)
                              in
                           (let uu____87273 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87273
                            then
                              let uu____87278 =
                                let uu____87280 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____87280
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____87278
                            else ());
                           (let uu____87284 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____87284 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____87293 =
                                    let uu____87296 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _87299  ->
                                         FStar_Pervasives_Native.Some _87299)
                                      uu____87296
                                     in
                                  solve_prob orig uu____87293 [] wl1  in
                                let uu____87300 = attempt [base_prob] wl2  in
                                solve env uu____87300))))
           in
        let uu____87301 = FStar_Util.physical_equality c1 c2  in
        if uu____87301
        then
          let uu____87304 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____87304
        else
          ((let uu____87308 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____87308
            then
              let uu____87313 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____87315 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____87313
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____87315
            else ());
           (let uu____87320 =
              let uu____87329 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____87332 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____87329, uu____87332)  in
            match uu____87320 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87350),FStar_Syntax_Syntax.Total
                    (t2,uu____87352)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____87369 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87369 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87371,FStar_Syntax_Syntax.Total uu____87372) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87391),FStar_Syntax_Syntax.Total
                    (t2,uu____87393)) ->
                     let uu____87410 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87410 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87413),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87415)) ->
                     let uu____87432 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87432 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87435),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87437)) ->
                     let uu____87454 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87454 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87456,FStar_Syntax_Syntax.Comp uu____87457) ->
                     let uu____87466 =
                       let uu___4158_87469 = problem  in
                       let uu____87472 =
                         let uu____87473 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87473
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87469.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87472;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87469.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87469.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87469.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87469.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87469.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87469.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87469.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87469.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87466 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____87474,FStar_Syntax_Syntax.Comp uu____87475) ->
                     let uu____87484 =
                       let uu___4158_87487 = problem  in
                       let uu____87490 =
                         let uu____87491 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87491
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87487.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87490;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87487.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87487.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87487.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87487.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87487.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87487.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87487.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87487.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87484 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87492,FStar_Syntax_Syntax.GTotal uu____87493) ->
                     let uu____87502 =
                       let uu___4170_87505 = problem  in
                       let uu____87508 =
                         let uu____87509 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87509
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87505.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87505.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87505.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87508;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87505.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87505.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87505.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87505.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87505.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87505.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87502 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87510,FStar_Syntax_Syntax.Total uu____87511) ->
                     let uu____87520 =
                       let uu___4170_87523 = problem  in
                       let uu____87526 =
                         let uu____87527 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87527
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87523.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87523.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87523.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87526;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87523.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87523.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87523.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87523.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87523.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87523.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87520 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87528,FStar_Syntax_Syntax.Comp uu____87529) ->
                     let uu____87530 =
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
                     if uu____87530
                     then
                       let uu____87533 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____87533 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____87540 =
                            let uu____87545 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____87545
                            then (c1_comp, c2_comp)
                            else
                              (let uu____87554 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____87555 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____87554, uu____87555))
                             in
                          match uu____87540 with
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
                           (let uu____87563 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87563
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____87571 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____87571 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____87574 =
                                  let uu____87576 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____87578 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____87576 uu____87578
                                   in
                                giveup env uu____87574 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____87589 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____87589 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____87639 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____87639 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____87664 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____87695  ->
                match uu____87695 with
                | (u1,u2) ->
                    let uu____87703 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____87705 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____87703 uu____87705))
         in
      FStar_All.pipe_right uu____87664 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____87742,[])) when
          let uu____87769 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____87769 -> "{}"
      | uu____87772 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____87799 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____87799
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____87811 =
              FStar_List.map
                (fun uu____87824  ->
                   match uu____87824 with
                   | (uu____87831,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____87811 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____87842 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____87842 imps
  
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
                  let uu____87899 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____87899
                  then
                    let uu____87907 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____87909 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____87907
                      (rel_to_string rel) uu____87909
                  else "TOP"  in
                let uu____87915 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____87915 with
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
              let uu____87975 =
                let uu____87978 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _87981  -> FStar_Pervasives_Native.Some _87981)
                  uu____87978
                 in
              FStar_Syntax_Syntax.new_bv uu____87975 t1  in
            let uu____87982 =
              let uu____87987 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____87987
               in
            match uu____87982 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____88047 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____88047
         then
           let uu____88052 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____88052
         else ());
        (let uu____88059 =
           FStar_Util.record_time (fun uu____88066  -> solve env probs)  in
         match uu____88059 with
         | (sol,ms) ->
             ((let uu____88078 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____88078
               then
                 let uu____88083 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____88083
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____88096 =
                     FStar_Util.record_time
                       (fun uu____88103  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____88096 with
                    | ((),ms1) ->
                        ((let uu____88114 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____88114
                          then
                            let uu____88119 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____88119
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____88133 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____88133
                     then
                       let uu____88140 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____88140
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____88167 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____88167
            then
              let uu____88172 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____88172
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____88179 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____88179
             then
               let uu____88184 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____88184
             else ());
            (let f2 =
               let uu____88190 =
                 let uu____88191 = FStar_Syntax_Util.unmeta f1  in
                 uu____88191.FStar_Syntax_Syntax.n  in
               match uu____88190 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____88195 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_88196 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_88196.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_88196.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_88196.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicit
        Prims.list) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____88251 =
              let uu____88252 =
                let uu____88253 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _88254  ->
                       FStar_TypeChecker_Common.NonTrivial _88254)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____88253;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____88252  in
            FStar_All.pipe_left
              (fun _88261  -> FStar_Pervasives_Native.Some _88261)
              uu____88251
  
let with_guard_no_simp :
  'Auu____88271 .
    'Auu____88271 ->
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
            let uu____88294 =
              let uu____88295 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _88296  -> FStar_TypeChecker_Common.NonTrivial _88296)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____88295;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____88294
  
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
          (let uu____88329 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____88329
           then
             let uu____88334 = FStar_Syntax_Print.term_to_string t1  in
             let uu____88336 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____88334
               uu____88336
           else ());
          (let uu____88341 =
             let uu____88346 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____88346
              in
           match uu____88341 with
           | (prob,wl) ->
               let g =
                 let uu____88354 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____88364  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____88354  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____88400 = try_teq true env t1 t2  in
        match uu____88400 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____88405 = FStar_TypeChecker_Env.get_range env  in
              let uu____88406 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____88405 uu____88406);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____88414 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____88414
              then
                let uu____88419 = FStar_Syntax_Print.term_to_string t1  in
                let uu____88421 = FStar_Syntax_Print.term_to_string t2  in
                let uu____88423 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____88419
                  uu____88421 uu____88423
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
          let uu____88449 = FStar_TypeChecker_Env.get_range env  in
          let uu____88450 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____88449 uu____88450
  
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
        (let uu____88479 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____88479
         then
           let uu____88484 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____88486 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____88484 uu____88486
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____88497 =
           let uu____88504 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____88504 "sub_comp"
            in
         match uu____88497 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____88517 =
                 FStar_Util.record_time
                   (fun uu____88529  ->
                      let uu____88530 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____88541  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____88530)
                  in
               match uu____88517 with
               | (r,ms) ->
                   ((let uu____88572 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____88572
                     then
                       let uu____88577 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____88579 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____88581 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____88577 uu____88579
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____88581
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
      fun uu____88619  ->
        match uu____88619 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____88662 =
                 let uu____88668 =
                   let uu____88670 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____88672 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____88670 uu____88672
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____88668)  in
               let uu____88676 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____88662 uu____88676)
               in
            let equiv1 v1 v' =
              let uu____88689 =
                let uu____88694 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____88695 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____88694, uu____88695)  in
              match uu____88689 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____88715 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____88746 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____88746 with
                      | FStar_Syntax_Syntax.U_unif uu____88753 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____88782  ->
                                    match uu____88782 with
                                    | (u,v') ->
                                        let uu____88791 = equiv1 v1 v'  in
                                        if uu____88791
                                        then
                                          let uu____88796 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____88796 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____88817 -> []))
               in
            let uu____88822 =
              let wl =
                let uu___4377_88826 = empty_worklist env  in
                {
                  attempting = (uu___4377_88826.attempting);
                  wl_deferred = (uu___4377_88826.wl_deferred);
                  ctr = (uu___4377_88826.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_88826.smt_ok);
                  umax_heuristic_ok = (uu___4377_88826.umax_heuristic_ok);
                  tcenv = (uu___4377_88826.tcenv);
                  wl_implicits = (uu___4377_88826.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____88845  ->
                      match uu____88845 with
                      | (lb,v1) ->
                          let uu____88852 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____88852 with
                           | USolved wl1 -> ()
                           | uu____88855 -> fail1 lb v1)))
               in
            let rec check_ineq uu____88866 =
              match uu____88866 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____88878) -> true
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
                      uu____88902,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____88904,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____88915) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____88923,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____88932 -> false)
               in
            let uu____88938 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____88955  ->
                      match uu____88955 with
                      | (u,v1) ->
                          let uu____88963 = check_ineq (u, v1)  in
                          if uu____88963
                          then true
                          else
                            ((let uu____88971 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____88971
                              then
                                let uu____88976 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____88978 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____88976
                                  uu____88978
                              else ());
                             false)))
               in
            if uu____88938
            then ()
            else
              ((let uu____88988 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____88988
                then
                  ((let uu____88994 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____88994);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____89006 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____89006))
                else ());
               (let uu____89019 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____89019))
  
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
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____89093 =
          match uu____89093 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_89119 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_89119.attempting);
            wl_deferred = (uu___4454_89119.wl_deferred);
            ctr = (uu___4454_89119.ctr);
            defer_ok;
            smt_ok = (uu___4454_89119.smt_ok);
            umax_heuristic_ok = (uu___4454_89119.umax_heuristic_ok);
            tcenv = (uu___4454_89119.tcenv);
            wl_implicits = (uu___4454_89119.wl_implicits)
          }  in
        (let uu____89122 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____89122
         then
           let uu____89127 = FStar_Util.string_of_bool defer_ok  in
           let uu____89129 = wl_to_string wl  in
           let uu____89131 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____89127 uu____89129 uu____89131
         else ());
        (let g1 =
           let uu____89137 = solve_and_commit env wl fail1  in
           match uu____89137 with
           | FStar_Pervasives_Native.Some
               (uu____89144::uu____89145,uu____89146) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_89175 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_89175.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_89175.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____89176 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_89185 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_89185.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_89185.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_89185.FStar_TypeChecker_Env.implicits)
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
    let uu____89228 = FStar_ST.op_Bang last_proof_ns  in
    match uu____89228 with
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
            let uu___4493_89353 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_89353.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_89353.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_89353.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____89354 =
            let uu____89356 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____89356  in
          if uu____89354
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____89368 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____89369 =
                       let uu____89371 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____89371
                        in
                     FStar_Errors.diag uu____89368 uu____89369)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____89379 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____89380 =
                        let uu____89382 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____89382
                         in
                      FStar_Errors.diag uu____89379 uu____89380)
                   else ();
                   (let uu____89388 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____89388
                      "discharge_guard'" env vc1);
                   (let uu____89390 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____89390 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____89399 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89400 =
                                let uu____89402 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____89402
                                 in
                              FStar_Errors.diag uu____89399 uu____89400)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____89412 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89413 =
                                let uu____89415 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____89415
                                 in
                              FStar_Errors.diag uu____89412 uu____89413)
                           else ();
                           (let vcs =
                              let uu____89429 = FStar_Options.use_tactics ()
                                 in
                              if uu____89429
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____89451  ->
                                     (let uu____89453 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____89453);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____89497  ->
                                              match uu____89497 with
                                              | (env1,goal,opts) ->
                                                  let uu____89513 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____89513, opts)))))
                              else
                                (let uu____89516 =
                                   let uu____89523 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____89523)  in
                                 [uu____89516])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____89556  ->
                                    match uu____89556 with
                                    | (env1,goal,opts) ->
                                        let uu____89566 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____89566 with
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
                                                (let uu____89578 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89579 =
                                                   let uu____89581 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____89583 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____89581 uu____89583
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89578 uu____89579)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____89590 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89591 =
                                                   let uu____89593 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____89593
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89590 uu____89591)
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
      let uu____89611 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____89611 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____89620 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____89620
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____89634 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____89634 with
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
        let uu____89664 = try_teq false env t1 t2  in
        match uu____89664 with
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
          let rec unresolved ctx_u =
            let uu____89708 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____89708 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____89721 ->
                     let uu____89734 =
                       let uu____89735 = FStar_Syntax_Subst.compress r  in
                       uu____89735.FStar_Syntax_Syntax.n  in
                     (match uu____89734 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____89740) ->
                          unresolved ctx_u'
                      | uu____89757 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____89781 = acc  in
            match uu____89781 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____89800 = hd1  in
                     (match uu____89800 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____89811 = unresolved ctx_u  in
                             if uu____89811
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____89835 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____89835
                                     then
                                       let uu____89839 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____89839
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____89848 = teq_nosmt env1 t tm
                                          in
                                       match uu____89848 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_89858 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_89858.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_89858.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_89858.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_89858.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_89858.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_89858.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_89858.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_89866 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_89866.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_89866.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_89866.FStar_TypeChecker_Env.imp_range)
                                       }  in
                                     until_fixpoint (out, true) (hd2 ::
                                       (FStar_List.append extra tl1))))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4613_89877 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_89877.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_89877.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_89877.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_89877.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_89877.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_89877.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_89877.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_89877.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_89877.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_89877.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_89877.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_89877.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_89877.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_89877.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_89877.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_89877.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_89877.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_89877.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_89877.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_89877.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_89877.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_89877.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_89877.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_89877.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_89877.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_89877.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_89877.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_89877.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_89877.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_89877.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_89877.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_89877.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_89877.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_89877.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_89877.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_89877.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_89877.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_89877.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_89877.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_89877.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_89877.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_89877.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_89881 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_89881.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_89881.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_89881.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_89881.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_89881.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_89881.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_89881.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_89881.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_89881.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_89881.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_89881.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_89881.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_89881.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_89881.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_89881.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_89881.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_89881.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_89881.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_89881.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_89881.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_89881.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_89881.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_89881.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_89881.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_89881.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_89881.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_89881.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_89881.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_89881.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_89881.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_89881.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_89881.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_89881.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_89881.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_89881.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_89881.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_89881.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_89881.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_89881.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_89881.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_89881.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_89881.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____89886 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____89886
                                   then
                                     let uu____89891 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____89893 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____89895 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____89897 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____89891 uu____89893 uu____89895
                                       reason uu____89897
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_89904  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____89911 =
                                             let uu____89921 =
                                               let uu____89929 =
                                                 let uu____89931 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____89933 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____89935 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____89931 uu____89933
                                                   uu____89935
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____89929, r)
                                                in
                                             [uu____89921]  in
                                           FStar_Errors.add_errors
                                             uu____89911);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_89955 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_89955.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_89955.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_89955.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____89959 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____89970  ->
                                               let uu____89971 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____89973 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____89975 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____89971 uu____89973
                                                 reason uu____89975)) env2 g2
                                         true
                                        in
                                     match uu____89959 with
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
          let uu___4640_89983 = g  in
          let uu____89984 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_89983.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_89983.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_89983.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____89984
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
        let uu____90027 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____90027 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____90028 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____90028
      | imp::uu____90030 ->
          let uu____90033 =
            let uu____90039 =
              let uu____90041 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____90043 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____90041 uu____90043 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____90039)
             in
          FStar_Errors.raise_error uu____90033
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90065 = teq_nosmt env t1 t2  in
        match uu____90065 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_90084 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_90084.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_90084.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_90084.FStar_TypeChecker_Env.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____90120 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90120
         then
           let uu____90125 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90127 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____90125
             uu____90127
         else ());
        (let uu____90132 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90132 with
         | (prob,x,wl) ->
             let g =
               let uu____90151 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____90162  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90151  in
             ((let uu____90183 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____90183
               then
                 let uu____90188 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____90190 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____90192 =
                   let uu____90194 = FStar_Util.must g  in
                   guard_to_string env uu____90194  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____90188 uu____90190 uu____90192
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
        let uu____90231 = check_subtyping env t1 t2  in
        match uu____90231 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90250 =
              let uu____90251 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____90251 g  in
            FStar_Pervasives_Native.Some uu____90250
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90270 = check_subtyping env t1 t2  in
        match uu____90270 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90289 =
              let uu____90290 =
                let uu____90291 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____90291]  in
              FStar_TypeChecker_Env.close_guard env uu____90290 g  in
            FStar_Pervasives_Native.Some uu____90289
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____90329 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90329
         then
           let uu____90334 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90336 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____90334
             uu____90336
         else ());
        (let uu____90341 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90341 with
         | (prob,x,wl) ->
             let g =
               let uu____90356 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____90367  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90356  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____90391 =
                      let uu____90392 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____90392]  in
                    FStar_TypeChecker_Env.close_guard env uu____90391 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90433 = subtype_nosmt env t1 t2  in
        match uu____90433 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  