open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____60299 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____60334 -> false
  
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
                    let uu____60757 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____60757;
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
                     (let uu___656_60789 = wl  in
                      {
                        attempting = (uu___656_60789.attempting);
                        wl_deferred = (uu___656_60789.wl_deferred);
                        ctr = (uu___656_60789.ctr);
                        defer_ok = (uu___656_60789.defer_ok);
                        smt_ok = (uu___656_60789.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_60789.umax_heuristic_ok);
                        tcenv = (uu___656_60789.tcenv);
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
            let uu___662_60822 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_60822.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_60822.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_60822.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_60822.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_60822.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_60822.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_60822.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_60822.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_60822.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_60822.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_60822.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_60822.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_60822.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_60822.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_60822.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_60822.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_60822.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_60822.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_60822.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_60822.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_60822.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_60822.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_60822.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_60822.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_60822.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_60822.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_60822.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_60822.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_60822.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_60822.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_60822.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_60822.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_60822.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_60822.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_60822.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_60822.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_60822.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_60822.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_60822.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_60822.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_60822.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_60822.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____60824 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____60824 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____60867 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____60903 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____60936 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____60947 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____60958 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_60976  ->
    match uu___585_60976 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____60988 = FStar_Syntax_Util.head_and_args t  in
    match uu____60988 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____61051 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____61053 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____61068 =
                     let uu____61070 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____61070  in
                   FStar_Util.format1 "@<%s>" uu____61068
                in
             let uu____61074 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____61051 uu____61053 uu____61074
         | uu____61077 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_61089  ->
      match uu___586_61089 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____61094 =
            let uu____61098 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____61100 =
              let uu____61104 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____61106 =
                let uu____61110 =
                  let uu____61114 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____61114]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____61110
                 in
              uu____61104 :: uu____61106  in
            uu____61098 :: uu____61100  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____61094
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61125 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____61127 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____61129 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____61125
            uu____61127 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____61129
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_61143  ->
      match uu___587_61143 with
      | UNIV (u,t) ->
          let x =
            let uu____61149 = FStar_Options.hide_uvar_nums ()  in
            if uu____61149
            then "?"
            else
              (let uu____61156 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____61156 FStar_Util.string_of_int)
             in
          let uu____61160 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____61160
      | TERM (u,t) ->
          let x =
            let uu____61167 = FStar_Options.hide_uvar_nums ()  in
            if uu____61167
            then "?"
            else
              (let uu____61174 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____61174 FStar_Util.string_of_int)
             in
          let uu____61178 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____61178
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____61197 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____61197 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____61218 =
      let uu____61222 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____61222
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____61218 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____61241 .
    (FStar_Syntax_Syntax.term * 'Auu____61241) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____61260 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____61281  ->
              match uu____61281 with
              | (x,uu____61288) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____61260 (FStar_String.concat " ")
  
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
        (let uu____61331 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____61331
         then
           let uu____61336 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____61336
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_61347  ->
    match uu___588_61347 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____61353 .
    'Auu____61353 FStar_TypeChecker_Common.problem ->
      'Auu____61353 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_61365 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_61365.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_61365.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_61365.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_61365.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_61365.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_61365.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_61365.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____61373 .
    'Auu____61373 FStar_TypeChecker_Common.problem ->
      'Auu____61373 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_61393  ->
    match uu___589_61393 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61399  -> FStar_TypeChecker_Common.TProb _61399)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _61405  -> FStar_TypeChecker_Common.CProb _61405)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_61411  ->
    match uu___590_61411 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_61417 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_61417.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_61417.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_61417.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_61417.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_61417.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_61417.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_61417.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_61417.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_61417.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_61425 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_61425.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_61425.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_61425.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_61425.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_61425.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_61425.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_61425.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_61425.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_61425.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_61438  ->
      match uu___591_61438 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_61445  ->
    match uu___592_61445 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_61458  ->
    match uu___593_61458 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_61473  ->
    match uu___594_61473 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_61488  ->
    match uu___595_61488 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_61502  ->
    match uu___596_61502 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_61516  ->
    match uu___597_61516 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_61528  ->
    match uu___598_61528 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____61544 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____61544) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____61574 =
          let uu____61576 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61576  in
        if uu____61574
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____61613)::bs ->
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
          let uu____61660 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61684 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61684]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61660
      | FStar_TypeChecker_Common.CProb p ->
          let uu____61712 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____61736 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____61736]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____61712
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____61783 =
          let uu____61785 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61785  in
        if uu____61783
        then ()
        else
          (let uu____61790 =
             let uu____61793 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____61793
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____61790 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____61842 =
          let uu____61844 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____61844  in
        if uu____61842
        then ()
        else
          (let uu____61849 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____61849)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____61869 =
        let uu____61871 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____61871  in
      if uu____61869
      then ()
      else
        (let msgf m =
           let uu____61885 =
             let uu____61887 =
               let uu____61889 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____61889 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____61887  in
           Prims.op_Hat msg uu____61885  in
         (let uu____61894 = msgf "scope"  in
          let uu____61897 = p_scope prob  in
          def_scope_wf uu____61894 (p_loc prob) uu____61897);
         (let uu____61909 = msgf "guard"  in
          def_check_scoped uu____61909 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____61916 = msgf "lhs"  in
                def_check_scoped uu____61916 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61919 = msgf "rhs"  in
                def_check_scoped uu____61919 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____61926 = msgf "lhs"  in
                def_check_scoped_comp uu____61926 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____61929 = msgf "rhs"  in
                def_check_scoped_comp uu____61929 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_61950 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_61950.wl_deferred);
          ctr = (uu___831_61950.ctr);
          defer_ok = (uu___831_61950.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_61950.umax_heuristic_ok);
          tcenv = (uu___831_61950.tcenv);
          wl_implicits = (uu___831_61950.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____61958 .
    FStar_TypeChecker_Env.env ->
      ('Auu____61958 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_61981 = empty_worklist env  in
      let uu____61982 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____61982;
        wl_deferred = (uu___835_61981.wl_deferred);
        ctr = (uu___835_61981.ctr);
        defer_ok = (uu___835_61981.defer_ok);
        smt_ok = (uu___835_61981.smt_ok);
        umax_heuristic_ok = (uu___835_61981.umax_heuristic_ok);
        tcenv = (uu___835_61981.tcenv);
        wl_implicits = (uu___835_61981.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_62005 = wl  in
        {
          attempting = (uu___840_62005.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_62005.ctr);
          defer_ok = (uu___840_62005.defer_ok);
          smt_ok = (uu___840_62005.smt_ok);
          umax_heuristic_ok = (uu___840_62005.umax_heuristic_ok);
          tcenv = (uu___840_62005.tcenv);
          wl_implicits = (uu___840_62005.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_62033 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_62033.wl_deferred);
         ctr = (uu___845_62033.ctr);
         defer_ok = (uu___845_62033.defer_ok);
         smt_ok = (uu___845_62033.smt_ok);
         umax_heuristic_ok = (uu___845_62033.umax_heuristic_ok);
         tcenv = (uu___845_62033.tcenv);
         wl_implicits = (uu___845_62033.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____62047 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62047 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____62081 = FStar_Syntax_Util.type_u ()  in
            match uu____62081 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____62093 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____62093 with
                 | (uu____62111,tt,wl1) ->
                     let uu____62114 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____62114, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_62120  ->
    match uu___599_62120 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _62126  -> FStar_TypeChecker_Common.TProb _62126) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _62132  -> FStar_TypeChecker_Common.CProb _62132) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____62140 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____62140 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____62160  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____62202 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____62202 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____62202 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____62202 FStar_TypeChecker_Common.problem *
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
                        let uu____62289 =
                          let uu____62298 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62298]  in
                        FStar_List.append scope uu____62289
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____62341 =
                      let uu____62344 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____62344  in
                    FStar_List.append uu____62341
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____62363 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62363 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____62389 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62389;
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
                  (let uu____62463 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62463 with
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
                  (let uu____62551 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____62551 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____62589 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____62589 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____62589 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____62589 FStar_TypeChecker_Common.problem *
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
                          let uu____62657 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____62657]  in
                        let uu____62676 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____62676
                     in
                  let uu____62679 =
                    let uu____62686 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_62697 = wl  in
                       {
                         attempting = (uu___928_62697.attempting);
                         wl_deferred = (uu___928_62697.wl_deferred);
                         ctr = (uu___928_62697.ctr);
                         defer_ok = (uu___928_62697.defer_ok);
                         smt_ok = (uu___928_62697.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_62697.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_62697.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____62686
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____62679 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____62715 =
                              let uu____62720 =
                                let uu____62721 =
                                  let uu____62730 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____62730
                                   in
                                [uu____62721]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____62720
                               in
                            uu____62715 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____62758 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____62758;
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
                let uu____62806 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____62806;
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
  'Auu____62821 .
    worklist ->
      'Auu____62821 FStar_TypeChecker_Common.problem ->
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
              let uu____62854 =
                let uu____62857 =
                  let uu____62858 =
                    let uu____62865 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____62865)  in
                  FStar_Syntax_Syntax.NT uu____62858  in
                [uu____62857]  in
              FStar_Syntax_Subst.subst uu____62854 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____62889 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____62889
        then
          let uu____62897 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____62900 = prob_to_string env d  in
          let uu____62902 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____62897 uu____62900 uu____62902 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____62918 -> failwith "impossible"  in
           let uu____62921 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____62937 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62939 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62937, uu____62939)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____62946 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____62948 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____62946, uu____62948)
              in
           match uu____62921 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_62976  ->
            match uu___600_62976 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____62988 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____62992 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____62992 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_63023  ->
           match uu___601_63023 with
           | UNIV uu____63026 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____63033 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____63033
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
        (fun uu___602_63061  ->
           match uu___602_63061 with
           | UNIV (u',t) ->
               let uu____63066 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____63066
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____63073 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63085 =
        let uu____63086 =
          let uu____63087 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____63087
           in
        FStar_Syntax_Subst.compress uu____63086  in
      FStar_All.pipe_right uu____63085 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63099 =
        let uu____63100 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____63100  in
      FStar_All.pipe_right uu____63099 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____63108 = FStar_Syntax_Util.head_and_args t  in
    match uu____63108 with
    | (h,uu____63127) ->
        let uu____63152 =
          let uu____63153 = FStar_Syntax_Subst.compress h  in
          uu____63153.FStar_Syntax_Syntax.n  in
        (match uu____63152 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____63158 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____63171 = should_strongly_reduce t  in
      if uu____63171
      then
        let uu____63174 =
          let uu____63175 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____63175  in
        FStar_All.pipe_right uu____63174 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____63185 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____63185) ->
        (FStar_Syntax_Syntax.term * 'Auu____63185)
  =
  fun env  ->
    fun t  ->
      let uu____63208 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____63208, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____63260  ->
              match uu____63260 with
              | (x,imp) ->
                  let uu____63279 =
                    let uu___1025_63280 = x  in
                    let uu____63281 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_63280.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_63280.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____63281
                    }  in
                  (uu____63279, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____63305 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____63305
        | FStar_Syntax_Syntax.U_max us ->
            let uu____63309 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____63309
        | uu____63312 -> u2  in
      let uu____63313 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____63313
  
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
                (let uu____63434 = norm_refinement env t12  in
                 match uu____63434 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____63449;
                     FStar_Syntax_Syntax.vars = uu____63450;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____63474 =
                       let uu____63476 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____63478 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____63476 uu____63478
                        in
                     failwith uu____63474)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____63494 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____63494
          | FStar_Syntax_Syntax.Tm_uinst uu____63495 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63532 =
                   let uu____63533 = FStar_Syntax_Subst.compress t1'  in
                   uu____63533.FStar_Syntax_Syntax.n  in
                 match uu____63532 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63548 -> aux true t1'
                 | uu____63556 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____63571 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63602 =
                   let uu____63603 = FStar_Syntax_Subst.compress t1'  in
                   uu____63603.FStar_Syntax_Syntax.n  in
                 match uu____63602 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63618 -> aux true t1'
                 | uu____63626 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____63641 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____63688 =
                   let uu____63689 = FStar_Syntax_Subst.compress t1'  in
                   uu____63689.FStar_Syntax_Syntax.n  in
                 match uu____63688 with
                 | FStar_Syntax_Syntax.Tm_refine uu____63704 -> aux true t1'
                 | uu____63712 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____63727 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____63742 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____63757 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____63772 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____63787 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____63816 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____63849 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____63870 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____63897 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____63925 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____63962 ->
              let uu____63969 =
                let uu____63971 = FStar_Syntax_Print.term_to_string t12  in
                let uu____63973 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____63971 uu____63973
                 in
              failwith uu____63969
          | FStar_Syntax_Syntax.Tm_ascribed uu____63988 ->
              let uu____64015 =
                let uu____64017 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64019 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64017 uu____64019
                 in
              failwith uu____64015
          | FStar_Syntax_Syntax.Tm_delayed uu____64034 ->
              let uu____64057 =
                let uu____64059 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64061 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64059 uu____64061
                 in
              failwith uu____64057
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____64076 =
                let uu____64078 = FStar_Syntax_Print.term_to_string t12  in
                let uu____64080 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____64078 uu____64080
                 in
              failwith uu____64076
           in
        let uu____64095 = whnf env t1  in aux false uu____64095
  
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
      let uu____64156 = base_and_refinement env t  in
      FStar_All.pipe_right uu____64156 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____64197 = FStar_Syntax_Syntax.null_bv t  in
    (uu____64197, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____64224 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____64224 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____64284  ->
    match uu____64284 with
    | (t_base,refopt) ->
        let uu____64315 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____64315 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____64357 =
      let uu____64361 =
        let uu____64364 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____64391  ->
                  match uu____64391 with | (uu____64400,uu____64401,x) -> x))
           in
        FStar_List.append wl.attempting uu____64364  in
      FStar_List.map (wl_prob_to_string wl) uu____64361  in
    FStar_All.pipe_right uu____64357 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____64424 .
    ('Auu____64424 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____64436  ->
    match uu____64436 with
    | (uu____64443,c,args) ->
        let uu____64446 = print_ctx_uvar c  in
        let uu____64448 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____64446 uu____64448
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____64458 = FStar_Syntax_Util.head_and_args t  in
    match uu____64458 with
    | (head1,_args) ->
        let uu____64502 =
          let uu____64503 = FStar_Syntax_Subst.compress head1  in
          uu____64503.FStar_Syntax_Syntax.n  in
        (match uu____64502 with
         | FStar_Syntax_Syntax.Tm_uvar uu____64507 -> true
         | uu____64521 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____64529 = FStar_Syntax_Util.head_and_args t  in
    match uu____64529 with
    | (head1,_args) ->
        let uu____64572 =
          let uu____64573 = FStar_Syntax_Subst.compress head1  in
          uu____64573.FStar_Syntax_Syntax.n  in
        (match uu____64572 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____64577) -> u
         | uu____64594 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____64619 = FStar_Syntax_Util.head_and_args t  in
      match uu____64619 with
      | (head1,args) ->
          let uu____64666 =
            let uu____64667 = FStar_Syntax_Subst.compress head1  in
            uu____64667.FStar_Syntax_Syntax.n  in
          (match uu____64666 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____64675)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____64708 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_64733  ->
                         match uu___603_64733 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____64738 =
                               let uu____64739 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____64739.FStar_Syntax_Syntax.n  in
                             (match uu____64738 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____64744 -> false)
                         | uu____64746 -> true))
                  in
               (match uu____64708 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____64771 =
                        FStar_List.collect
                          (fun uu___604_64783  ->
                             match uu___604_64783 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____64787 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____64787]
                             | uu____64788 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____64771 FStar_List.rev  in
                    let uu____64811 =
                      let uu____64818 =
                        let uu____64827 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_64849  ->
                                  match uu___605_64849 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____64853 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____64853]
                                  | uu____64854 -> []))
                           in
                        FStar_All.pipe_right uu____64827 FStar_List.rev  in
                      let uu____64877 =
                        let uu____64880 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____64880  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____64818 uu____64877
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____64811 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____64916  ->
                                match uu____64916 with
                                | (x,i) ->
                                    let uu____64935 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____64935, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____64966  ->
                                match uu____64966 with
                                | (a,i) ->
                                    let uu____64985 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____64985, i)) args_sol
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
           | uu____65007 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____65029 =
          let uu____65052 =
            let uu____65053 = FStar_Syntax_Subst.compress k  in
            uu____65053.FStar_Syntax_Syntax.n  in
          match uu____65052 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____65135 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____65135)
              else
                (let uu____65170 = FStar_Syntax_Util.abs_formals t  in
                 match uu____65170 with
                 | (ys',t1,uu____65203) ->
                     let uu____65208 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____65208))
          | uu____65247 ->
              let uu____65248 =
                let uu____65253 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____65253)  in
              ((ys, t), uu____65248)
           in
        match uu____65029 with
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
                 let uu____65348 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____65348 c  in
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
               (let uu____65426 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____65426
                then
                  let uu____65431 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____65433 = print_ctx_uvar uv  in
                  let uu____65435 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____65431 uu____65433 uu____65435
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____65444 =
                   let uu____65446 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____65446  in
                 let uu____65449 =
                   let uu____65452 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____65452
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____65444 uu____65449 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____65485 =
               let uu____65486 =
                 let uu____65488 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____65490 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____65488 uu____65490
                  in
               failwith uu____65486  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____65556  ->
                       match uu____65556 with
                       | (a,i) ->
                           let uu____65577 =
                             let uu____65578 = FStar_Syntax_Subst.compress a
                                in
                             uu____65578.FStar_Syntax_Syntax.n  in
                           (match uu____65577 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____65604 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____65614 =
                 let uu____65616 = is_flex g  in
                 Prims.op_Negation uu____65616  in
               if uu____65614
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____65625 = destruct_flex_t g wl  in
                  match uu____65625 with
                  | ((uu____65630,uv1,args),wl1) ->
                      ((let uu____65635 = args_as_binders args  in
                        assign_solution uu____65635 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_65637 = wl1  in
              {
                attempting = (uu___1277_65637.attempting);
                wl_deferred = (uu___1277_65637.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_65637.defer_ok);
                smt_ok = (uu___1277_65637.smt_ok);
                umax_heuristic_ok = (uu___1277_65637.umax_heuristic_ok);
                tcenv = (uu___1277_65637.tcenv);
                wl_implicits = (uu___1277_65637.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____65662 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____65662
         then
           let uu____65667 = FStar_Util.string_of_int pid  in
           let uu____65669 =
             let uu____65671 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____65671 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____65667
             uu____65669
         else ());
        commit sol;
        (let uu___1285_65685 = wl  in
         {
           attempting = (uu___1285_65685.attempting);
           wl_deferred = (uu___1285_65685.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_65685.defer_ok);
           smt_ok = (uu___1285_65685.smt_ok);
           umax_heuristic_ok = (uu___1285_65685.umax_heuristic_ok);
           tcenv = (uu___1285_65685.tcenv);
           wl_implicits = (uu___1285_65685.wl_implicits)
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
             | (uu____65751,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____65779 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____65779
              in
           (let uu____65785 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____65785
            then
              let uu____65790 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____65794 =
                let uu____65796 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____65796 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____65790
                uu____65794
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
        let uu____65831 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____65831 FStar_Util.set_elements  in
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
      let uu____65871 = occurs uk t  in
      match uu____65871 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____65910 =
                 let uu____65912 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____65914 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____65912 uu____65914
                  in
               FStar_Pervasives_Native.Some uu____65910)
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
            let uu____66034 = maximal_prefix bs_tail bs'_tail  in
            (match uu____66034 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____66085 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____66142  ->
             match uu____66142 with
             | (x,uu____66154) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____66172 = FStar_List.last bs  in
      match uu____66172 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____66196) ->
          let uu____66207 =
            FStar_Util.prefix_until
              (fun uu___606_66222  ->
                 match uu___606_66222 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____66225 -> false) g
             in
          (match uu____66207 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____66239,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____66276 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____66276 with
        | (pfx,uu____66286) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____66298 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____66298 with
             | (uu____66306,src',wl1) ->
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
                 | uu____66420 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____66421 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____66485  ->
                  fun uu____66486  ->
                    match (uu____66485, uu____66486) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____66589 =
                          let uu____66591 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____66591
                           in
                        if uu____66589
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____66625 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____66625
                           then
                             let uu____66642 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____66642)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____66421 with | (isect,uu____66692) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____66728 'Auu____66729 .
    (FStar_Syntax_Syntax.bv * 'Auu____66728) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____66729) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____66787  ->
              fun uu____66788  ->
                match (uu____66787, uu____66788) with
                | ((a,uu____66807),(b,uu____66809)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____66825 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____66825) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____66856  ->
           match uu____66856 with
           | (y,uu____66863) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____66873 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____66873) Prims.list ->
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
                   let uu____67035 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____67035
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____67068 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____67120 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____67164 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____67185 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_67193  ->
    match uu___607_67193 with
    | MisMatch (d1,d2) ->
        let uu____67205 =
          let uu____67207 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____67209 =
            let uu____67211 =
              let uu____67213 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____67213 ")"  in
            Prims.op_Hat ") (" uu____67211  in
          Prims.op_Hat uu____67207 uu____67209  in
        Prims.op_Hat "MisMatch (" uu____67205
    | HeadMatch u ->
        let uu____67220 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____67220
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_67229  ->
    match uu___608_67229 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____67246 -> HeadMatch false
  
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
          let uu____67268 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____67268 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____67279 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____67303 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____67313 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____67340 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____67340
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____67341 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____67342 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____67343 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____67356 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____67370 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____67394) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____67400,uu____67401) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____67443) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____67468;
             FStar_Syntax_Syntax.index = uu____67469;
             FStar_Syntax_Syntax.sort = t2;_},uu____67471)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____67479 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____67480 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____67481 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____67496 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____67503 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____67523 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____67523
  
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
           { FStar_Syntax_Syntax.blob = uu____67542;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67543;
             FStar_Syntax_Syntax.ltyp = uu____67544;
             FStar_Syntax_Syntax.rng = uu____67545;_},uu____67546)
            ->
            let uu____67557 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____67557 t21
        | (uu____67558,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____67559;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____67560;
             FStar_Syntax_Syntax.ltyp = uu____67561;
             FStar_Syntax_Syntax.rng = uu____67562;_})
            ->
            let uu____67573 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____67573
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____67585 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____67585
            then FullMatch
            else
              (let uu____67590 =
                 let uu____67599 =
                   let uu____67602 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____67602  in
                 let uu____67603 =
                   let uu____67606 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____67606  in
                 (uu____67599, uu____67603)  in
               MisMatch uu____67590)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____67612),FStar_Syntax_Syntax.Tm_uinst (g,uu____67614)) ->
            let uu____67623 = head_matches env f g  in
            FStar_All.pipe_right uu____67623 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____67624) -> HeadMatch true
        | (uu____67626,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____67630 = FStar_Const.eq_const c d  in
            if uu____67630
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____67640),FStar_Syntax_Syntax.Tm_uvar (uv',uu____67642)) ->
            let uu____67675 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____67675
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____67685),FStar_Syntax_Syntax.Tm_refine (y,uu____67687)) ->
            let uu____67696 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67696 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____67698),uu____67699) ->
            let uu____67704 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____67704 head_match
        | (uu____67705,FStar_Syntax_Syntax.Tm_refine (x,uu____67707)) ->
            let uu____67712 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____67712 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____67713,FStar_Syntax_Syntax.Tm_type uu____67714) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____67716,FStar_Syntax_Syntax.Tm_arrow uu____67717) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____67748),FStar_Syntax_Syntax.Tm_app
           (head',uu____67750)) ->
            let uu____67799 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____67799 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____67801),uu____67802) ->
            let uu____67827 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____67827 head_match
        | (uu____67828,FStar_Syntax_Syntax.Tm_app (head1,uu____67830)) ->
            let uu____67855 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____67855 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____67856,FStar_Syntax_Syntax.Tm_let
           uu____67857) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____67885,FStar_Syntax_Syntax.Tm_match uu____67886) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____67932,FStar_Syntax_Syntax.Tm_abs
           uu____67933) -> HeadMatch true
        | uu____67971 ->
            let uu____67976 =
              let uu____67985 = delta_depth_of_term env t11  in
              let uu____67988 = delta_depth_of_term env t21  in
              (uu____67985, uu____67988)  in
            MisMatch uu____67976
  
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
            (let uu____68054 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68054
             then
               let uu____68059 = FStar_Syntax_Print.term_to_string t  in
               let uu____68061 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____68059 uu____68061
             else ());
            (let uu____68066 =
               let uu____68067 = FStar_Syntax_Util.un_uinst head1  in
               uu____68067.FStar_Syntax_Syntax.n  in
             match uu____68066 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68073 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____68073 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____68087 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____68087
                        then
                          let uu____68092 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____68092
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____68097 ->
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
                      let uu____68114 =
                        let uu____68116 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____68116 = FStar_Syntax_Util.Equal  in
                      if uu____68114
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____68123 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____68123
                          then
                            let uu____68128 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____68130 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____68128 uu____68130
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____68135 -> FStar_Pervasives_Native.None)
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
            (let uu____68287 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____68287
             then
               let uu____68292 = FStar_Syntax_Print.term_to_string t11  in
               let uu____68294 = FStar_Syntax_Print.term_to_string t21  in
               let uu____68296 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____68292
                 uu____68294 uu____68296
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____68324 =
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
               match uu____68324 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____68372 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____68372 with
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
                  uu____68410),uu____68411)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68432 =
                      let uu____68441 = maybe_inline t11  in
                      let uu____68444 = maybe_inline t21  in
                      (uu____68441, uu____68444)  in
                    match uu____68432 with
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
                 (uu____68487,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____68488))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____68509 =
                      let uu____68518 = maybe_inline t11  in
                      let uu____68521 = maybe_inline t21  in
                      (uu____68518, uu____68521)  in
                    match uu____68509 with
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
             | MisMatch uu____68576 -> fail1 n_delta r t11 t21
             | uu____68585 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____68600 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____68600
           then
             let uu____68605 = FStar_Syntax_Print.term_to_string t1  in
             let uu____68607 = FStar_Syntax_Print.term_to_string t2  in
             let uu____68609 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____68617 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____68634 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____68634
                    (fun uu____68669  ->
                       match uu____68669 with
                       | (t11,t21) ->
                           let uu____68677 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____68679 =
                             let uu____68681 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____68681  in
                           Prims.op_Hat uu____68677 uu____68679))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____68605 uu____68607 uu____68609 uu____68617
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____68698 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____68698 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_68713  ->
    match uu___609_68713 with
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
      let uu___1789_68762 = p  in
      let uu____68765 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____68766 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_68762.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____68765;
        FStar_TypeChecker_Common.relation =
          (uu___1789_68762.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____68766;
        FStar_TypeChecker_Common.element =
          (uu___1789_68762.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_68762.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_68762.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_68762.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_68762.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_68762.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____68781 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____68781
            (fun _68786  -> FStar_TypeChecker_Common.TProb _68786)
      | FStar_TypeChecker_Common.CProb uu____68787 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____68810 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____68810 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____68818 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____68818 with
           | (lh,lhs_args) ->
               let uu____68865 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____68865 with
                | (rh,rhs_args) ->
                    let uu____68912 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____68925,FStar_Syntax_Syntax.Tm_uvar uu____68926)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____69015 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69042,uu____69043)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____69058,FStar_Syntax_Syntax.Tm_uvar uu____69059)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69074,FStar_Syntax_Syntax.Tm_arrow
                         uu____69075) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69105 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69105.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69105.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69105.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69105.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69105.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69105.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69105.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69105.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69105.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____69108,FStar_Syntax_Syntax.Tm_type uu____69109)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69125 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69125.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69125.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69125.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69125.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69125.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69125.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69125.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69125.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69125.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____69128,FStar_Syntax_Syntax.Tm_uvar uu____69129)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_69145 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_69145.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_69145.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_69145.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_69145.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_69145.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_69145.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_69145.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_69145.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_69145.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____69148,FStar_Syntax_Syntax.Tm_uvar uu____69149)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____69164,uu____69165)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____69180,FStar_Syntax_Syntax.Tm_uvar uu____69181)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____69196,uu____69197) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____68912 with
                     | (rank,tp1) ->
                         let uu____69210 =
                           FStar_All.pipe_right
                             (let uu___1860_69214 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_69214.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_69214.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_69214.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_69214.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_69214.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_69214.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_69214.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_69214.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_69214.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _69217  ->
                                FStar_TypeChecker_Common.TProb _69217)
                            in
                         (rank, uu____69210))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____69221 =
            FStar_All.pipe_right
              (let uu___1864_69225 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_69225.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_69225.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_69225.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_69225.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_69225.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_69225.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_69225.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_69225.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_69225.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _69228  -> FStar_TypeChecker_Common.CProb _69228)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____69221)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____69288 probs =
      match uu____69288 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____69369 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____69390 = rank wl.tcenv hd1  in
               (match uu____69390 with
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
                      (let uu____69451 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____69456 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____69456)
                          in
                       if uu____69451
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
          let uu____69529 = FStar_Syntax_Util.head_and_args t  in
          match uu____69529 with
          | (hd1,uu____69548) ->
              let uu____69573 =
                let uu____69574 = FStar_Syntax_Subst.compress hd1  in
                uu____69574.FStar_Syntax_Syntax.n  in
              (match uu____69573 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____69579) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____69614  ->
                           match uu____69614 with
                           | (y,uu____69623) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____69646  ->
                                       match uu____69646 with
                                       | (x,uu____69655) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____69660 -> false)
           in
        let uu____69662 = rank tcenv p  in
        match uu____69662 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____69671 -> true
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
    match projectee with | UDeferred _0 -> true | uu____69708 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____69727 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____69747 -> false
  
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
                        let uu____69809 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____69809 with
                        | (k,uu____69817) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____69830 -> false)))
            | uu____69832 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____69884 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____69892 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____69892 = (Prims.parse_int "0")))
                           in
                        if uu____69884 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____69913 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____69921 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____69921 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____69913)
               in
            let uu____69925 = filter1 u12  in
            let uu____69928 = filter1 u22  in (uu____69925, uu____69928)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____69963 = filter_out_common_univs us1 us2  in
                   (match uu____69963 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____70023 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____70023 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____70026 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____70037 =
                             let uu____70039 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____70041 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____70039 uu____70041
                              in
                           UFailed uu____70037))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70067 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70067 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____70093 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____70093 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____70096 ->
                   let uu____70101 =
                     let uu____70103 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____70105 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____70103 uu____70105 msg
                      in
                   UFailed uu____70101)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____70108,uu____70109) ->
              let uu____70111 =
                let uu____70113 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70115 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70113 uu____70115
                 in
              failwith uu____70111
          | (FStar_Syntax_Syntax.U_unknown ,uu____70118) ->
              let uu____70119 =
                let uu____70121 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70123 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70121 uu____70123
                 in
              failwith uu____70119
          | (uu____70126,FStar_Syntax_Syntax.U_bvar uu____70127) ->
              let uu____70129 =
                let uu____70131 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70133 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70131 uu____70133
                 in
              failwith uu____70129
          | (uu____70136,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____70137 =
                let uu____70139 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____70141 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____70139 uu____70141
                 in
              failwith uu____70137
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____70171 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____70171
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____70188 = occurs_univ v1 u3  in
              if uu____70188
              then
                let uu____70191 =
                  let uu____70193 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70195 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70193 uu____70195
                   in
                try_umax_components u11 u21 uu____70191
              else
                (let uu____70200 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70200)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____70212 = occurs_univ v1 u3  in
              if uu____70212
              then
                let uu____70215 =
                  let uu____70217 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____70219 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____70217 uu____70219
                   in
                try_umax_components u11 u21 uu____70215
              else
                (let uu____70224 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____70224)
          | (FStar_Syntax_Syntax.U_max uu____70225,uu____70226) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70234 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70234
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____70240,FStar_Syntax_Syntax.U_max uu____70241) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____70249 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____70249
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____70255,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____70257,FStar_Syntax_Syntax.U_name uu____70258) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____70260) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____70262) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70264,FStar_Syntax_Syntax.U_succ uu____70265) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____70267,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____70374 = bc1  in
      match uu____70374 with
      | (bs1,mk_cod1) ->
          let uu____70418 = bc2  in
          (match uu____70418 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____70529 = aux xs ys  in
                     (match uu____70529 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____70612 =
                       let uu____70619 = mk_cod1 xs  in ([], uu____70619)  in
                     let uu____70622 =
                       let uu____70629 = mk_cod2 ys  in ([], uu____70629)  in
                     (uu____70612, uu____70622)
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
                  let uu____70698 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____70698 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____70701 =
                    let uu____70702 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____70702 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____70701
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____70707 = has_type_guard t1 t2  in (uu____70707, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____70708 = has_type_guard t2 t1  in (uu____70708, wl)
  
let is_flex_pat :
  'Auu____70718 'Auu____70719 'Auu____70720 .
    ('Auu____70718 * 'Auu____70719 * 'Auu____70720 Prims.list) -> Prims.bool
  =
  fun uu___610_70734  ->
    match uu___610_70734 with
    | (uu____70743,uu____70744,[]) -> true
    | uu____70748 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____70781 = f  in
      match uu____70781 with
      | (uu____70788,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____70789;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____70790;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____70793;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____70794;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____70795;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____70796;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____70866  ->
                 match uu____70866 with
                 | (y,uu____70875) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____71029 =
                  let uu____71044 =
                    let uu____71047 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71047  in
                  ((FStar_List.rev pat_binders), uu____71044)  in
                FStar_Pervasives_Native.Some uu____71029
            | (uu____71080,[]) ->
                let uu____71111 =
                  let uu____71126 =
                    let uu____71129 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____71129  in
                  ((FStar_List.rev pat_binders), uu____71126)  in
                FStar_Pervasives_Native.Some uu____71111
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____71220 =
                  let uu____71221 = FStar_Syntax_Subst.compress a  in
                  uu____71221.FStar_Syntax_Syntax.n  in
                (match uu____71220 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____71241 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____71241
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_71271 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_71271.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_71271.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____71275 =
                            let uu____71276 =
                              let uu____71283 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____71283)  in
                            FStar_Syntax_Syntax.NT uu____71276  in
                          [uu____71275]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_71299 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_71299.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_71299.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____71300 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____71340 =
                  let uu____71355 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____71355  in
                (match uu____71340 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____71430 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____71463 ->
               let uu____71464 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____71464 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____71786 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____71786
       then
         let uu____71791 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____71791
       else ());
      (let uu____71796 = next_prob probs  in
       match uu____71796 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_71823 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_71823.wl_deferred);
               ctr = (uu___2219_71823.ctr);
               defer_ok = (uu___2219_71823.defer_ok);
               smt_ok = (uu___2219_71823.smt_ok);
               umax_heuristic_ok = (uu___2219_71823.umax_heuristic_ok);
               tcenv = (uu___2219_71823.tcenv);
               wl_implicits = (uu___2219_71823.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____71832 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____71832
                 then
                   let uu____71835 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____71835
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
                           (let uu___2231_71847 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_71847.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_71847.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_71847.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_71847.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_71847.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_71847.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_71847.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_71847.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_71847.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____71873 ->
                let uu____71884 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____71955  ->
                          match uu____71955 with
                          | (c,uu____71966,uu____71967) -> c < probs.ctr))
                   in
                (match uu____71884 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____72022 =
                            let uu____72027 =
                              FStar_List.map
                                (fun uu____72045  ->
                                   match uu____72045 with
                                   | (uu____72059,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____72027, (probs.wl_implicits))  in
                          Success uu____72022
                      | uu____72067 ->
                          let uu____72078 =
                            let uu___2249_72079 = probs  in
                            let uu____72080 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____72103  ->
                                      match uu____72103 with
                                      | (uu____72112,uu____72113,y) -> y))
                               in
                            {
                              attempting = uu____72080;
                              wl_deferred = rest;
                              ctr = (uu___2249_72079.ctr);
                              defer_ok = (uu___2249_72079.defer_ok);
                              smt_ok = (uu___2249_72079.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_72079.umax_heuristic_ok);
                              tcenv = (uu___2249_72079.tcenv);
                              wl_implicits = (uu___2249_72079.wl_implicits)
                            }  in
                          solve env uu____72078))))

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
            let uu____72124 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____72124 with
            | USolved wl1 ->
                let uu____72126 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____72126
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
                  let uu____72180 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____72180 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____72183 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____72196;
                  FStar_Syntax_Syntax.vars = uu____72197;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____72200;
                  FStar_Syntax_Syntax.vars = uu____72201;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____72214,uu____72215) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____72223,FStar_Syntax_Syntax.Tm_uinst uu____72224) ->
                failwith "Impossible: expect head symbols to match"
            | uu____72232 -> USolved wl

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
            ((let uu____72244 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____72244
              then
                let uu____72249 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____72249 msg
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
               let uu____72341 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____72341 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____72396 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____72396
                then
                  let uu____72401 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____72403 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____72401 uu____72403
                else ());
               (let uu____72408 = head_matches_delta env1 wl2 t1 t2  in
                match uu____72408 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____72454 = eq_prob t1 t2 wl2  in
                         (match uu____72454 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____72475 ->
                         let uu____72484 = eq_prob t1 t2 wl2  in
                         (match uu____72484 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____72534 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____72549 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____72550 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____72549, uu____72550)
                           | FStar_Pervasives_Native.None  ->
                               let uu____72555 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____72556 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____72555, uu____72556)
                            in
                         (match uu____72534 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____72587 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____72587 with
                                | (t1_hd,t1_args) ->
                                    let uu____72632 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____72632 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____72698 =
                                              let uu____72705 =
                                                let uu____72716 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____72716 :: t1_args  in
                                              let uu____72733 =
                                                let uu____72742 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____72742 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____72791  ->
                                                   fun uu____72792  ->
                                                     fun uu____72793  ->
                                                       match (uu____72791,
                                                               uu____72792,
                                                               uu____72793)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____72843),
                                                          (a2,uu____72845))
                                                           ->
                                                           let uu____72882 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____72882
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____72705
                                                uu____72733
                                               in
                                            match uu____72698 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_72908 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_72908.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_72908.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_72908.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____72920 =
                                                  solve env1 wl'  in
                                                (match uu____72920 with
                                                 | Success (uu____72923,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_72927
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_72927.attempting);
                                                            wl_deferred =
                                                              (uu___2412_72927.wl_deferred);
                                                            ctr =
                                                              (uu___2412_72927.ctr);
                                                            defer_ok =
                                                              (uu___2412_72927.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_72927.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_72927.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_72927.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____72928 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____72961 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____72961 with
                                | (t1_base,p1_opt) ->
                                    let uu____72997 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____72997 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____73096 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____73096
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
                                               let uu____73149 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____73149
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
                                               let uu____73181 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73181
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
                                               let uu____73213 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____73213
                                           | uu____73216 -> t_base  in
                                         let uu____73233 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____73233 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____73247 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____73247, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____73254 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____73254 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____73290 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____73290 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____73326 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____73326
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
                              let uu____73350 = combine t11 t21 wl2  in
                              (match uu____73350 with
                               | (t12,ps,wl3) ->
                                   ((let uu____73383 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____73383
                                     then
                                       let uu____73388 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____73388
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____73430 ts1 =
               match uu____73430 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____73493 = pairwise out t wl2  in
                        (match uu____73493 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____73529 =
               let uu____73540 = FStar_List.hd ts  in (uu____73540, [], wl1)
                in
             let uu____73549 = FStar_List.tl ts  in
             aux uu____73529 uu____73549  in
           let uu____73556 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____73556 with
           | (this_flex,this_rigid) ->
               let uu____73582 =
                 let uu____73583 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____73583.FStar_Syntax_Syntax.n  in
               (match uu____73582 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____73608 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____73608
                    then
                      let uu____73611 = destruct_flex_t this_flex wl  in
                      (match uu____73611 with
                       | (flex,wl1) ->
                           let uu____73618 = quasi_pattern env flex  in
                           (match uu____73618 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____73637 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____73637
                                  then
                                    let uu____73642 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____73642
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____73649 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_73652 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_73652.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_73652.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_73652.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_73652.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_73652.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_73652.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_73652.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_73652.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_73652.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____73649)
                | uu____73653 ->
                    ((let uu____73655 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____73655
                      then
                        let uu____73660 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____73660
                      else ());
                     (let uu____73665 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____73665 with
                      | (u,_args) ->
                          let uu____73708 =
                            let uu____73709 = FStar_Syntax_Subst.compress u
                               in
                            uu____73709.FStar_Syntax_Syntax.n  in
                          (match uu____73708 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____73737 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____73737 with
                                 | (u',uu____73756) ->
                                     let uu____73781 =
                                       let uu____73782 = whnf env u'  in
                                       uu____73782.FStar_Syntax_Syntax.n  in
                                     (match uu____73781 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____73804 -> false)
                                  in
                               let uu____73806 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_73829  ->
                                         match uu___611_73829 with
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
                                              | uu____73843 -> false)
                                         | uu____73847 -> false))
                                  in
                               (match uu____73806 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____73862 = whnf env this_rigid
                                         in
                                      let uu____73863 =
                                        FStar_List.collect
                                          (fun uu___612_73869  ->
                                             match uu___612_73869 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____73875 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____73875]
                                             | uu____73879 -> [])
                                          bounds_probs
                                         in
                                      uu____73862 :: uu____73863  in
                                    let uu____73880 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____73880 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____73913 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____73928 =
                                               let uu____73929 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____73929.FStar_Syntax_Syntax.n
                                                in
                                             match uu____73928 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____73941 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____73941)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____73952 -> bound  in
                                           let uu____73953 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____73953)  in
                                         (match uu____73913 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____73988 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____73988
                                                then
                                                  let wl'1 =
                                                    let uu___2574_73994 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_73994.wl_deferred);
                                                      ctr =
                                                        (uu___2574_73994.ctr);
                                                      defer_ok =
                                                        (uu___2574_73994.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_73994.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_73994.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_73994.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_73994.wl_implicits)
                                                    }  in
                                                  let uu____73995 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____73995
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____74001 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_74003 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_74003.wl_deferred);
                                                       ctr =
                                                         (uu___2579_74003.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_74003.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_74003.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_74003.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____74001 with
                                                | Success (uu____74005,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_74008 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_74008.wl_deferred);
                                                        ctr =
                                                          (uu___2585_74008.ctr);
                                                        defer_ok =
                                                          (uu___2585_74008.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_74008.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_74008.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_74008.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_74008.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_74010 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_74010.attempting);
                                                        wl_deferred =
                                                          (uu___2588_74010.wl_deferred);
                                                        ctr =
                                                          (uu___2588_74010.ctr);
                                                        defer_ok =
                                                          (uu___2588_74010.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_74010.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_74010.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_74010.tcenv);
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
                                                    let uu____74026 =
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
                                                    ((let uu____74040 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____74040
                                                      then
                                                        let uu____74045 =
                                                          let uu____74047 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____74047
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____74045
                                                      else ());
                                                     (let uu____74060 =
                                                        let uu____74075 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____74075)
                                                         in
                                                      match uu____74060 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____74097))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74123 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74123
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
                                                                  let uu____74143
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74143))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____74168 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____74168
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
                                                                    let uu____74188
                                                                    =
                                                                    let uu____74193
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____74193
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____74188
                                                                    [] wl2
                                                                     in
                                                                  let uu____74199
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____74199))))
                                                      | uu____74200 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____74216 when flip ->
                               let uu____74217 =
                                 let uu____74219 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74221 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____74219 uu____74221
                                  in
                               failwith uu____74217
                           | uu____74224 ->
                               let uu____74225 =
                                 let uu____74227 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____74229 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____74227 uu____74229
                                  in
                               failwith uu____74225)))))

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
                      (fun uu____74265  ->
                         match uu____74265 with
                         | (x,i) ->
                             let uu____74284 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____74284, i)) bs_lhs
                     in
                  let uu____74287 = lhs  in
                  match uu____74287 with
                  | (uu____74288,u_lhs,uu____74290) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____74387 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____74397 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____74397, univ)
                             in
                          match uu____74387 with
                          | (k,univ) ->
                              let uu____74404 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____74404 with
                               | (uu____74421,u,wl3) ->
                                   let uu____74424 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____74424, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____74450 =
                              let uu____74463 =
                                let uu____74474 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____74474 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____74525  ->
                                   fun uu____74526  ->
                                     match (uu____74525, uu____74526) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____74627 =
                                           let uu____74634 =
                                             let uu____74637 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____74637
                                              in
                                           copy_uvar u_lhs [] uu____74634 wl2
                                            in
                                         (match uu____74627 with
                                          | (uu____74666,t_a,wl3) ->
                                              let uu____74669 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____74669 with
                                               | (uu____74688,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____74463
                                ([], wl1)
                               in
                            (match uu____74450 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_74744 = ct  in
                                   let uu____74745 =
                                     let uu____74748 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____74748
                                      in
                                   let uu____74763 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_74744.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_74744.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____74745;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____74763;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_74744.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_74781 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_74781.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_74781.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____74784 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____74784 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____74846 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____74846 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____74857 =
                                          let uu____74862 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____74862)  in
                                        TERM uu____74857  in
                                      let uu____74863 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____74863 with
                                       | (sub_prob,wl3) ->
                                           let uu____74877 =
                                             let uu____74878 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____74878
                                              in
                                           solve env uu____74877))
                             | (x,imp)::formals2 ->
                                 let uu____74900 =
                                   let uu____74907 =
                                     let uu____74910 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____74910
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____74907 wl1
                                    in
                                 (match uu____74900 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____74931 =
                                          let uu____74934 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____74934
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____74931 u_x
                                         in
                                      let uu____74935 =
                                        let uu____74938 =
                                          let uu____74941 =
                                            let uu____74942 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____74942, imp)  in
                                          [uu____74941]  in
                                        FStar_List.append bs_terms
                                          uu____74938
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____74935 formals2 wl2)
                              in
                           let uu____74969 = occurs_check u_lhs arrow1  in
                           (match uu____74969 with
                            | (uu____74982,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____74998 =
                                    let uu____75000 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____75000
                                     in
                                  giveup_or_defer env orig wl uu____74998
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
              (let uu____75033 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____75033
               then
                 let uu____75038 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____75041 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____75038 (rel_to_string (p_rel orig)) uu____75041
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____75168 = rhs wl1 scope env1 subst1  in
                     (match uu____75168 with
                      | (rhs_prob,wl2) ->
                          ((let uu____75189 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____75189
                            then
                              let uu____75194 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____75194
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____75272 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____75272 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_75274 = hd1  in
                       let uu____75275 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_75274.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_75274.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75275
                       }  in
                     let hd21 =
                       let uu___2773_75279 = hd2  in
                       let uu____75280 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_75279.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_75279.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____75280
                       }  in
                     let uu____75283 =
                       let uu____75288 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____75288
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____75283 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____75309 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____75309
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____75316 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____75316 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____75383 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____75383
                                  in
                               ((let uu____75401 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____75401
                                 then
                                   let uu____75406 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____75408 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____75406
                                     uu____75408
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____75441 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____75477 = aux wl [] env [] bs1 bs2  in
               match uu____75477 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____75532 = attempt sub_probs wl2  in
                   solve env uu____75532)

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
            let uu___2808_75553 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_75553.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_75553.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____75566 = try_solve env wl'  in
          match uu____75566 with
          | Success (uu____75567,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_75571 = wl  in
                  {
                    attempting = (uu___2817_75571.attempting);
                    wl_deferred = (uu___2817_75571.wl_deferred);
                    ctr = (uu___2817_75571.ctr);
                    defer_ok = (uu___2817_75571.defer_ok);
                    smt_ok = (uu___2817_75571.smt_ok);
                    umax_heuristic_ok = (uu___2817_75571.umax_heuristic_ok);
                    tcenv = (uu___2817_75571.tcenv);
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
        (let uu____75583 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____75583 wl)

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
              let uu____75597 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____75597 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____75631 = lhs1  in
              match uu____75631 with
              | (uu____75634,ctx_u,uu____75636) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____75644 ->
                        let uu____75645 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____75645 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____75694 = quasi_pattern env1 lhs1  in
              match uu____75694 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____75728) ->
                  let uu____75733 = lhs1  in
                  (match uu____75733 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____75748 = occurs_check ctx_u rhs1  in
                       (match uu____75748 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____75799 =
                                let uu____75807 =
                                  let uu____75809 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____75809
                                   in
                                FStar_Util.Inl uu____75807  in
                              (uu____75799, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____75837 =
                                 let uu____75839 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____75839  in
                               if uu____75837
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____75866 =
                                    let uu____75874 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____75874  in
                                  let uu____75880 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____75866, uu____75880)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____75924 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____75924 with
              | (rhs_hd,args) ->
                  let uu____75967 = FStar_Util.prefix args  in
                  (match uu____75967 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____76039 = lhs1  in
                       (match uu____76039 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____76043 =
                              let uu____76054 =
                                let uu____76061 =
                                  let uu____76064 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____76064
                                   in
                                copy_uvar u_lhs [] uu____76061 wl1  in
                              match uu____76054 with
                              | (uu____76091,t_last_arg,wl2) ->
                                  let uu____76094 =
                                    let uu____76101 =
                                      let uu____76102 =
                                        let uu____76111 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____76111]  in
                                      FStar_List.append bs_lhs uu____76102
                                       in
                                    copy_uvar u_lhs uu____76101 t_res_lhs wl2
                                     in
                                  (match uu____76094 with
                                   | (uu____76146,lhs',wl3) ->
                                       let uu____76149 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____76149 with
                                        | (uu____76166,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____76043 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____76187 =
                                     let uu____76188 =
                                       let uu____76193 =
                                         let uu____76194 =
                                           let uu____76197 =
                                             let uu____76202 =
                                               let uu____76203 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____76203]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____76202
                                              in
                                           uu____76197
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____76194
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____76193)  in
                                     TERM uu____76188  in
                                   [uu____76187]  in
                                 let uu____76228 =
                                   let uu____76235 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____76235 with
                                   | (p1,wl3) ->
                                       let uu____76255 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____76255 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____76228 with
                                  | (sub_probs,wl3) ->
                                      let uu____76287 =
                                        let uu____76288 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____76288  in
                                      solve env1 uu____76287))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____76322 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____76322 with
                | (uu____76340,args) ->
                    (match args with | [] -> false | uu____76376 -> true)
                 in
              let is_arrow rhs2 =
                let uu____76395 =
                  let uu____76396 = FStar_Syntax_Subst.compress rhs2  in
                  uu____76396.FStar_Syntax_Syntax.n  in
                match uu____76395 with
                | FStar_Syntax_Syntax.Tm_arrow uu____76400 -> true
                | uu____76416 -> false  in
              let uu____76418 = quasi_pattern env1 lhs1  in
              match uu____76418 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76429 =
                    let uu____76431 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____76431
                     in
                  giveup_or_defer env1 orig1 wl1 uu____76429
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____76440 = is_app rhs1  in
                  if uu____76440
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____76445 = is_arrow rhs1  in
                     if uu____76445
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____76450 =
                          let uu____76452 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____76452
                           in
                        giveup_or_defer env1 orig1 wl1 uu____76450))
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
                let uu____76463 = lhs  in
                (match uu____76463 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____76467 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____76467 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____76485 =
                              let uu____76489 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____76489
                               in
                            FStar_All.pipe_right uu____76485
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____76510 = occurs_check ctx_uv rhs1  in
                          (match uu____76510 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____76539 =
                                   let uu____76541 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____76541
                                    in
                                 giveup_or_defer env orig wl uu____76539
                               else
                                 (let uu____76547 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____76547
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____76554 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____76554
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____76558 =
                                         let uu____76560 =
                                           names_to_string1 fvs2  in
                                         let uu____76562 =
                                           names_to_string1 fvs1  in
                                         let uu____76564 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____76560 uu____76562
                                           uu____76564
                                          in
                                       giveup_or_defer env orig wl
                                         uu____76558)
                                    else first_order orig env wl lhs rhs1))
                      | uu____76576 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____76583 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____76583 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____76609 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____76609
                             | (FStar_Util.Inl msg,uu____76611) ->
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
                  (let uu____76656 =
                     let uu____76673 = quasi_pattern env lhs  in
                     let uu____76680 = quasi_pattern env rhs  in
                     (uu____76673, uu____76680)  in
                   match uu____76656 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____76723 = lhs  in
                       (match uu____76723 with
                        | ({ FStar_Syntax_Syntax.n = uu____76724;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____76726;_},u_lhs,uu____76728)
                            ->
                            let uu____76731 = rhs  in
                            (match uu____76731 with
                             | (uu____76732,u_rhs,uu____76734) ->
                                 let uu____76735 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____76735
                                 then
                                   let uu____76742 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____76742
                                 else
                                   (let uu____76745 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____76745 with
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
                                        let uu____76777 =
                                          let uu____76784 =
                                            let uu____76787 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____76787
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____76784
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____76777 with
                                         | (uu____76799,w,wl1) ->
                                             let w_app =
                                               let uu____76805 =
                                                 let uu____76810 =
                                                   FStar_List.map
                                                     (fun uu____76821  ->
                                                        match uu____76821
                                                        with
                                                        | (z,uu____76829) ->
                                                            let uu____76834 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____76834) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____76810
                                                  in
                                               uu____76805
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____76836 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____76836
                                               then
                                                 let uu____76841 =
                                                   let uu____76845 =
                                                     flex_t_to_string lhs  in
                                                   let uu____76847 =
                                                     let uu____76851 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____76853 =
                                                       let uu____76857 =
                                                         term_to_string w  in
                                                       let uu____76859 =
                                                         let uu____76863 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____76872 =
                                                           let uu____76876 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____76885 =
                                                             let uu____76889
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____76889]
                                                              in
                                                           uu____76876 ::
                                                             uu____76885
                                                            in
                                                         uu____76863 ::
                                                           uu____76872
                                                          in
                                                       uu____76857 ::
                                                         uu____76859
                                                        in
                                                     uu____76851 ::
                                                       uu____76853
                                                      in
                                                   uu____76845 :: uu____76847
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____76841
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____76906 =
                                                     let uu____76911 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____76911)  in
                                                   TERM uu____76906  in
                                                 let uu____76912 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____76912
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____76920 =
                                                        let uu____76925 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____76925)
                                                         in
                                                      TERM uu____76920  in
                                                    [s1; s2])
                                                  in
                                               let uu____76926 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____76926))))))
                   | uu____76927 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____76998 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____76998
            then
              let uu____77003 = FStar_Syntax_Print.term_to_string t1  in
              let uu____77005 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____77007 = FStar_Syntax_Print.term_to_string t2  in
              let uu____77009 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____77003 uu____77005 uu____77007 uu____77009
            else ());
           (let uu____77020 = FStar_Syntax_Util.head_and_args t1  in
            match uu____77020 with
            | (head1,args1) ->
                let uu____77063 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____77063 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____77133 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____77133 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____77159 =
                         let uu____77161 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____77163 = args_to_string args1  in
                         let uu____77167 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____77169 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____77161 uu____77163 uu____77167 uu____77169
                          in
                       giveup env1 uu____77159 orig
                     else
                       (let uu____77176 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____77181 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____77181 = FStar_Syntax_Util.Equal)
                           in
                        if uu____77176
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_77185 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_77185.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_77185.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_77185.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_77185.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_77185.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_77185.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_77185.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_77185.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____77195 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____77195
                                    else solve env1 wl2))
                        else
                          (let uu____77200 = base_and_refinement env1 t1  in
                           match uu____77200 with
                           | (base1,refinement1) ->
                               let uu____77225 = base_and_refinement env1 t2
                                  in
                               (match uu____77225 with
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
                                           let uu____77390 =
                                             FStar_List.fold_right
                                               (fun uu____77430  ->
                                                  fun uu____77431  ->
                                                    match (uu____77430,
                                                            uu____77431)
                                                    with
                                                    | (((a1,uu____77483),
                                                        (a2,uu____77485)),
                                                       (probs,wl3)) ->
                                                        let uu____77534 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____77534
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____77390 with
                                           | (subprobs,wl3) ->
                                               ((let uu____77577 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77577
                                                 then
                                                   let uu____77582 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____77582
                                                 else ());
                                                (let uu____77588 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____77588
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
                                                    (let uu____77615 =
                                                       mk_sub_probs wl3  in
                                                     match uu____77615 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____77631 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____77631
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____77639 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____77639))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____77663 =
                                                    mk_sub_probs wl3  in
                                                  match uu____77663 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____77677 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____77677)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____77703 =
                                           match uu____77703 with
                                           | (prob,reason) ->
                                               ((let uu____77714 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____77714
                                                 then
                                                   let uu____77719 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____77721 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____77719 uu____77721
                                                     reason
                                                 else ());
                                                (let uu____77726 =
                                                   let uu____77735 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____77738 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____77735, uu____77738)
                                                    in
                                                 match uu____77726 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____77751 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____77751 with
                                                      | (head1',uu____77769)
                                                          ->
                                                          let uu____77794 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____77794
                                                           with
                                                           | (head2',uu____77812)
                                                               ->
                                                               let uu____77837
                                                                 =
                                                                 let uu____77842
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____77843
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____77842,
                                                                   uu____77843)
                                                                  in
                                                               (match uu____77837
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____77845
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77845
                                                                    then
                                                                    let uu____77850
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____77852
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____77854
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____77856
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____77850
                                                                    uu____77852
                                                                    uu____77854
                                                                    uu____77856
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____77861
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_77869
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_77869.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_77869.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_77869.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_77869.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_77869.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_77869.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_77869.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_77869.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____77871
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____77871
                                                                    then
                                                                    let uu____77876
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____77876
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____77881 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____77893 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____77893 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____77901 =
                                             let uu____77902 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____77902.FStar_Syntax_Syntax.n
                                              in
                                           match uu____77901 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____77907 -> false  in
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
                                          | uu____77910 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____77913 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_77949 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_77949.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_77949.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_77949.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_77949.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_77949.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_77949.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_77949.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_77949.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____78025 = destruct_flex_t scrutinee wl1  in
             match uu____78025 with
             | ((_t,uv,_args),wl2) ->
                 let uu____78036 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____78036 with
                  | (xs,pat_term,uu____78052,uu____78053) ->
                      let uu____78058 =
                        FStar_List.fold_left
                          (fun uu____78081  ->
                             fun x  ->
                               match uu____78081 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____78102 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____78102 with
                                    | (uu____78121,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____78058 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____78142 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____78142 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_78159 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_78159.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_78159.umax_heuristic_ok);
                                    tcenv = (uu___3212_78159.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____78171 = solve env1 wl'  in
                                (match uu____78171 with
                                 | Success (uu____78174,imps) ->
                                     let wl'1 =
                                       let uu___3220_78177 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_78177.wl_deferred);
                                         ctr = (uu___3220_78177.ctr);
                                         defer_ok =
                                           (uu___3220_78177.defer_ok);
                                         smt_ok = (uu___3220_78177.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_78177.umax_heuristic_ok);
                                         tcenv = (uu___3220_78177.tcenv);
                                         wl_implicits =
                                           (uu___3220_78177.wl_implicits)
                                       }  in
                                     let uu____78178 = solve env1 wl'1  in
                                     (match uu____78178 with
                                      | Success (uu____78181,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_78185 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_78185.attempting);
                                                 wl_deferred =
                                                   (uu___3228_78185.wl_deferred);
                                                 ctr = (uu___3228_78185.ctr);
                                                 defer_ok =
                                                   (uu___3228_78185.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_78185.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_78185.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_78185.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____78186 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____78193 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____78216 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____78216
                 then
                   let uu____78221 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____78223 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____78221 uu____78223
                 else ());
                (let uu____78228 =
                   let uu____78249 =
                     let uu____78258 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____78258)  in
                   let uu____78265 =
                     let uu____78274 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____78274)  in
                   (uu____78249, uu____78265)  in
                 match uu____78228 with
                 | ((uu____78304,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____78307;
                                   FStar_Syntax_Syntax.vars = uu____78308;_}),
                    (s,t)) ->
                     let uu____78379 =
                       let uu____78381 = is_flex scrutinee  in
                       Prims.op_Negation uu____78381  in
                     if uu____78379
                     then
                       ((let uu____78392 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____78392
                         then
                           let uu____78397 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____78397
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____78416 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78416
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____78431 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____78431
                           then
                             let uu____78436 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____78438 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____78436 uu____78438
                           else ());
                          (let pat_discriminates uu___613_78463 =
                             match uu___613_78463 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____78479;
                                  FStar_Syntax_Syntax.p = uu____78480;_},FStar_Pervasives_Native.None
                                ,uu____78481) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____78495;
                                  FStar_Syntax_Syntax.p = uu____78496;_},FStar_Pervasives_Native.None
                                ,uu____78497) -> true
                             | uu____78524 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____78627 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____78627 with
                                       | (uu____78629,uu____78630,t') ->
                                           let uu____78648 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____78648 with
                                            | (FullMatch ,uu____78660) ->
                                                true
                                            | (HeadMatch
                                               uu____78674,uu____78675) ->
                                                true
                                            | uu____78690 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____78727 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____78727
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____78738 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____78738 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____78826,uu____78827) ->
                                       branches1
                                   | uu____78972 -> branches  in
                                 let uu____79027 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79036 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79036 with
                                        | (p,uu____79040,uu____79041) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79070  -> FStar_Util.Inr _79070)
                                   uu____79027))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79100 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79100 with
                                | (p,uu____79109,e) ->
                                    ((let uu____79128 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79128
                                      then
                                        let uu____79133 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79135 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79133 uu____79135
                                      else ());
                                     (let uu____79140 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _79155  -> FStar_Util.Inr _79155)
                                        uu____79140)))))
                 | ((s,t),(uu____79158,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____79161;
                                         FStar_Syntax_Syntax.vars =
                                           uu____79162;_}))
                     ->
                     let uu____79231 =
                       let uu____79233 = is_flex scrutinee  in
                       Prims.op_Negation uu____79233  in
                     if uu____79231
                     then
                       ((let uu____79244 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____79244
                         then
                           let uu____79249 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____79249
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____79268 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79268
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____79283 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____79283
                           then
                             let uu____79288 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____79290 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____79288 uu____79290
                           else ());
                          (let pat_discriminates uu___613_79315 =
                             match uu___613_79315 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____79331;
                                  FStar_Syntax_Syntax.p = uu____79332;_},FStar_Pervasives_Native.None
                                ,uu____79333) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____79347;
                                  FStar_Syntax_Syntax.p = uu____79348;_},FStar_Pervasives_Native.None
                                ,uu____79349) -> true
                             | uu____79376 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____79479 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____79479 with
                                       | (uu____79481,uu____79482,t') ->
                                           let uu____79500 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____79500 with
                                            | (FullMatch ,uu____79512) ->
                                                true
                                            | (HeadMatch
                                               uu____79526,uu____79527) ->
                                                true
                                            | uu____79542 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____79579 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____79579
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____79590 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____79590 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____79678,uu____79679) ->
                                       branches1
                                   | uu____79824 -> branches  in
                                 let uu____79879 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____79888 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____79888 with
                                        | (p,uu____79892,uu____79893) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _79922  -> FStar_Util.Inr _79922)
                                   uu____79879))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____79952 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____79952 with
                                | (p,uu____79961,e) ->
                                    ((let uu____79980 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____79980
                                      then
                                        let uu____79985 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____79987 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____79985 uu____79987
                                      else ());
                                     (let uu____79992 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _80007  -> FStar_Util.Inr _80007)
                                        uu____79992)))))
                 | uu____80008 ->
                     ((let uu____80030 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____80030
                       then
                         let uu____80035 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____80037 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____80035 uu____80037
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____80083 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____80083
            then
              let uu____80088 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____80090 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____80092 = FStar_Syntax_Print.term_to_string t1  in
              let uu____80094 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____80088 uu____80090 uu____80092 uu____80094
            else ());
           (let uu____80099 = head_matches_delta env1 wl1 t1 t2  in
            match uu____80099 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____80130,uu____80131) ->
                     let rec may_relate head3 =
                       let uu____80159 =
                         let uu____80160 = FStar_Syntax_Subst.compress head3
                            in
                         uu____80160.FStar_Syntax_Syntax.n  in
                       match uu____80159 with
                       | FStar_Syntax_Syntax.Tm_name uu____80164 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____80166 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____80191 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____80191 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____80193 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____80196
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____80197 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____80200,uu____80201) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____80243) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____80249) ->
                           may_relate t
                       | uu____80254 -> false  in
                     let uu____80256 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____80256 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____80277 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____80277
                          then
                            let uu____80280 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____80280 with
                             | (guard,wl2) ->
                                 let uu____80287 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____80287)
                          else
                            (let uu____80290 =
                               let uu____80292 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____80294 =
                                 let uu____80296 =
                                   let uu____80300 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____80300
                                     (fun x  ->
                                        let uu____80307 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80307)
                                    in
                                 FStar_Util.dflt "" uu____80296  in
                               let uu____80312 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____80314 =
                                 let uu____80316 =
                                   let uu____80320 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____80320
                                     (fun x  ->
                                        let uu____80327 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____80327)
                                    in
                                 FStar_Util.dflt "" uu____80316  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____80292 uu____80294 uu____80312
                                 uu____80314
                                in
                             giveup env1 uu____80290 orig))
                 | (HeadMatch (true ),uu____80333) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____80348 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____80348 with
                        | (guard,wl2) ->
                            let uu____80355 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____80355)
                     else
                       (let uu____80358 =
                          let uu____80360 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____80362 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____80360 uu____80362
                           in
                        giveup env1 uu____80358 orig)
                 | (uu____80365,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_80379 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_80379.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_80379.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_80379.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_80379.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_80379.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_80379.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_80379.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_80379.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____80406 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____80406
          then
            let uu____80409 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____80409
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____80415 =
                let uu____80418 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80418  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____80415 t1);
             (let uu____80437 =
                let uu____80440 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____80440  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____80437 t2);
             (let uu____80459 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____80459
              then
                let uu____80463 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____80465 =
                  let uu____80467 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____80469 =
                    let uu____80471 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____80471  in
                  Prims.op_Hat uu____80467 uu____80469  in
                let uu____80474 =
                  let uu____80476 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____80478 =
                    let uu____80480 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____80480  in
                  Prims.op_Hat uu____80476 uu____80478  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____80463 uu____80465 uu____80474
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____80487,uu____80488) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____80512,FStar_Syntax_Syntax.Tm_delayed uu____80513) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____80537,uu____80538) ->
                  let uu____80565 =
                    let uu___3432_80566 = problem  in
                    let uu____80567 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_80566.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80567;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_80566.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_80566.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_80566.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_80566.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_80566.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_80566.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_80566.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_80566.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80565 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____80568,uu____80569) ->
                  let uu____80576 =
                    let uu___3438_80577 = problem  in
                    let uu____80578 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_80577.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____80578;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_80577.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_80577.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_80577.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_80577.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_80577.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_80577.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_80577.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_80577.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80576 wl
              | (uu____80579,FStar_Syntax_Syntax.Tm_ascribed uu____80580) ->
                  let uu____80607 =
                    let uu___3444_80608 = problem  in
                    let uu____80609 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_80608.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_80608.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_80608.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80609;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_80608.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_80608.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_80608.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_80608.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_80608.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_80608.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80607 wl
              | (uu____80610,FStar_Syntax_Syntax.Tm_meta uu____80611) ->
                  let uu____80618 =
                    let uu___3450_80619 = problem  in
                    let uu____80620 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_80619.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_80619.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_80619.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____80620;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_80619.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_80619.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_80619.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_80619.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_80619.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_80619.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____80618 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____80622),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____80624)) ->
                  let uu____80633 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____80633
              | (FStar_Syntax_Syntax.Tm_bvar uu____80634,uu____80635) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____80637,FStar_Syntax_Syntax.Tm_bvar uu____80638) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_80708 =
                    match uu___614_80708 with
                    | [] -> c
                    | bs ->
                        let uu____80736 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____80736
                     in
                  let uu____80747 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____80747 with
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
                                    let uu____80896 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____80896
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
                  let mk_t t l uu___615_80985 =
                    match uu___615_80985 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____81027 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____81027 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____81172 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____81173 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____81172
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____81173 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____81175,uu____81176) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81207 -> true
                    | uu____81227 -> false  in
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
                      (let uu____81287 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81295 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81295.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81295.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81295.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81295.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81295.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81295.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81295.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81295.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81295.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81295.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81295.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81295.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81295.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81295.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81295.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81295.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81295.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81295.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81295.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81295.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81295.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81295.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81295.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81295.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81295.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81295.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81295.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81295.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81295.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81295.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81295.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81295.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81295.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81295.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81295.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81295.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81295.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81295.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81295.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81295.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81287 with
                       | (uu____81300,ty,uu____81302) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81311 =
                                 let uu____81312 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81312.FStar_Syntax_Syntax.n  in
                               match uu____81311 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81315 ->
                                   let uu____81322 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81322
                               | uu____81323 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81326 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81326
                             then
                               let uu____81331 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81333 =
                                 let uu____81335 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81335
                                  in
                               let uu____81336 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81331 uu____81333 uu____81336
                             else ());
                            r1))
                     in
                  let uu____81341 =
                    let uu____81358 = maybe_eta t1  in
                    let uu____81365 = maybe_eta t2  in
                    (uu____81358, uu____81365)  in
                  (match uu____81341 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81407 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81407.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81407.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81407.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81407.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81407.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81407.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81407.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81407.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81428 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81428
                       then
                         let uu____81431 = destruct_flex_t not_abs wl  in
                         (match uu____81431 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81448 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81448.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81448.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81448.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81448.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81448.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81448.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81448.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81448.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81472 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81472
                       then
                         let uu____81475 = destruct_flex_t not_abs wl  in
                         (match uu____81475 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81492 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81492.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81492.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81492.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81492.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81492.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81492.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81492.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81492.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81496 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____81514,FStar_Syntax_Syntax.Tm_abs uu____81515) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____81546 -> true
                    | uu____81566 -> false  in
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
                      (let uu____81626 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_81634 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_81634.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_81634.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_81634.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_81634.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_81634.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_81634.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_81634.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_81634.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_81634.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_81634.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_81634.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_81634.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_81634.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_81634.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_81634.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_81634.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_81634.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_81634.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_81634.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_81634.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_81634.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_81634.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_81634.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_81634.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_81634.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_81634.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_81634.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_81634.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_81634.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_81634.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_81634.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_81634.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_81634.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_81634.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_81634.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_81634.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_81634.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_81634.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_81634.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_81634.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____81626 with
                       | (uu____81639,ty,uu____81641) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____81650 =
                                 let uu____81651 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____81651.FStar_Syntax_Syntax.n  in
                               match uu____81650 with
                               | FStar_Syntax_Syntax.Tm_refine uu____81654 ->
                                   let uu____81661 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____81661
                               | uu____81662 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____81665 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____81665
                             then
                               let uu____81670 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____81672 =
                                 let uu____81674 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____81674
                                  in
                               let uu____81675 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____81670 uu____81672 uu____81675
                             else ());
                            r1))
                     in
                  let uu____81680 =
                    let uu____81697 = maybe_eta t1  in
                    let uu____81704 = maybe_eta t2  in
                    (uu____81697, uu____81704)  in
                  (match uu____81680 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_81746 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_81746.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_81746.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_81746.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_81746.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_81746.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_81746.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_81746.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_81746.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____81767 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81767
                       then
                         let uu____81770 = destruct_flex_t not_abs wl  in
                         (match uu____81770 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81787 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81787.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81787.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81787.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81787.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81787.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81787.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81787.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81787.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____81811 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____81811
                       then
                         let uu____81814 = destruct_flex_t not_abs wl  in
                         (match uu____81814 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_81831 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_81831.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_81831.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_81831.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_81831.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_81831.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_81831.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_81831.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_81831.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____81835 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____81865 =
                    let uu____81870 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____81870 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_81898 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81898.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81898.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81900 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81900.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81900.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____81901,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_81916 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_81916.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_81916.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_81918 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_81918.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_81918.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____81919 -> (x1, x2)  in
                  (match uu____81865 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____81938 = as_refinement false env t11  in
                       (match uu____81938 with
                        | (x12,phi11) ->
                            let uu____81946 = as_refinement false env t21  in
                            (match uu____81946 with
                             | (x22,phi21) ->
                                 ((let uu____81955 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____81955
                                   then
                                     ((let uu____81960 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____81962 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81964 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____81960
                                         uu____81962 uu____81964);
                                      (let uu____81967 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____81969 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____81971 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____81967
                                         uu____81969 uu____81971))
                                   else ());
                                  (let uu____81976 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____81976 with
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
                                         let uu____82047 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____82047
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____82059 =
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
                                         (let uu____82072 =
                                            let uu____82075 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82075
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____82072
                                            (p_guard base_prob));
                                         (let uu____82094 =
                                            let uu____82097 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____82097
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____82094
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____82116 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____82116)
                                          in
                                       let has_uvars =
                                         (let uu____82121 =
                                            let uu____82123 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____82123
                                             in
                                          Prims.op_Negation uu____82121) ||
                                           (let uu____82127 =
                                              let uu____82129 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____82129
                                               in
                                            Prims.op_Negation uu____82127)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____82133 =
                                           let uu____82138 =
                                             let uu____82147 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____82147]  in
                                           mk_t_problem wl1 uu____82138 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____82133 with
                                          | (ref_prob,wl2) ->
                                              let uu____82169 =
                                                solve env1
                                                  (let uu___3657_82171 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_82171.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_82171.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_82171.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_82171.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_82171.wl_implicits)
                                                   })
                                                 in
                                              (match uu____82169 with
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
                                               | Success uu____82188 ->
                                                   let guard =
                                                     let uu____82196 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____82196
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_82205 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_82205.attempting);
                                                       wl_deferred =
                                                         (uu___3668_82205.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_82205.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_82205.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_82205.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_82205.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_82205.wl_implicits)
                                                     }  in
                                                   let uu____82207 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____82207))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82210,FStar_Syntax_Syntax.Tm_uvar uu____82211) ->
                  let uu____82236 = destruct_flex_t t1 wl  in
                  (match uu____82236 with
                   | (f1,wl1) ->
                       let uu____82243 = destruct_flex_t t2 wl1  in
                       (match uu____82243 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82250;
                    FStar_Syntax_Syntax.pos = uu____82251;
                    FStar_Syntax_Syntax.vars = uu____82252;_},uu____82253),FStar_Syntax_Syntax.Tm_uvar
                 uu____82254) ->
                  let uu____82303 = destruct_flex_t t1 wl  in
                  (match uu____82303 with
                   | (f1,wl1) ->
                       let uu____82310 = destruct_flex_t t2 wl1  in
                       (match uu____82310 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82317,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82318;
                    FStar_Syntax_Syntax.pos = uu____82319;
                    FStar_Syntax_Syntax.vars = uu____82320;_},uu____82321))
                  ->
                  let uu____82370 = destruct_flex_t t1 wl  in
                  (match uu____82370 with
                   | (f1,wl1) ->
                       let uu____82377 = destruct_flex_t t2 wl1  in
                       (match uu____82377 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82384;
                    FStar_Syntax_Syntax.pos = uu____82385;
                    FStar_Syntax_Syntax.vars = uu____82386;_},uu____82387),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82388;
                    FStar_Syntax_Syntax.pos = uu____82389;
                    FStar_Syntax_Syntax.vars = uu____82390;_},uu____82391))
                  ->
                  let uu____82464 = destruct_flex_t t1 wl  in
                  (match uu____82464 with
                   | (f1,wl1) ->
                       let uu____82471 = destruct_flex_t t2 wl1  in
                       (match uu____82471 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____82478,uu____82479) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82492 = destruct_flex_t t1 wl  in
                  (match uu____82492 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82499;
                    FStar_Syntax_Syntax.pos = uu____82500;
                    FStar_Syntax_Syntax.vars = uu____82501;_},uu____82502),uu____82503)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____82540 = destruct_flex_t t1 wl  in
                  (match uu____82540 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____82547,FStar_Syntax_Syntax.Tm_uvar uu____82548) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____82561,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82562;
                    FStar_Syntax_Syntax.pos = uu____82563;
                    FStar_Syntax_Syntax.vars = uu____82564;_},uu____82565))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____82602,FStar_Syntax_Syntax.Tm_arrow uu____82603) ->
                  solve_t' env
                    (let uu___3768_82631 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82631.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82631.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82631.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82631.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82631.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82631.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82631.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82631.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82631.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82632;
                    FStar_Syntax_Syntax.pos = uu____82633;
                    FStar_Syntax_Syntax.vars = uu____82634;_},uu____82635),FStar_Syntax_Syntax.Tm_arrow
                 uu____82636) ->
                  solve_t' env
                    (let uu___3768_82688 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_82688.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_82688.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_82688.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_82688.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_82688.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_82688.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_82688.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_82688.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_82688.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82689,FStar_Syntax_Syntax.Tm_uvar uu____82690) ->
                  let uu____82703 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82703
              | (uu____82704,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82705;
                    FStar_Syntax_Syntax.pos = uu____82706;
                    FStar_Syntax_Syntax.vars = uu____82707;_},uu____82708))
                  ->
                  let uu____82745 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82745
              | (FStar_Syntax_Syntax.Tm_uvar uu____82746,uu____82747) ->
                  let uu____82760 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82760
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____82761;
                    FStar_Syntax_Syntax.pos = uu____82762;
                    FStar_Syntax_Syntax.vars = uu____82763;_},uu____82764),uu____82765)
                  ->
                  let uu____82802 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____82802
              | (FStar_Syntax_Syntax.Tm_refine uu____82803,uu____82804) ->
                  let t21 =
                    let uu____82812 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____82812  in
                  solve_t env
                    (let uu___3803_82838 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_82838.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_82838.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_82838.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_82838.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_82838.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_82838.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_82838.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_82838.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_82838.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____82839,FStar_Syntax_Syntax.Tm_refine uu____82840) ->
                  let t11 =
                    let uu____82848 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____82848  in
                  solve_t env
                    (let uu___3810_82874 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_82874.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_82874.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_82874.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_82874.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_82874.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_82874.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_82874.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_82874.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_82874.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____82956 =
                    let uu____82957 = guard_of_prob env wl problem t1 t2  in
                    match uu____82957 with
                    | (guard,wl1) ->
                        let uu____82964 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____82964
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____83183 = br1  in
                        (match uu____83183 with
                         | (p1,w1,uu____83212) ->
                             let uu____83229 = br2  in
                             (match uu____83229 with
                              | (p2,w2,uu____83252) ->
                                  let uu____83257 =
                                    let uu____83259 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____83259  in
                                  if uu____83257
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____83286 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____83286 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____83323 = br2  in
                                         (match uu____83323 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____83356 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____83356
                                                 in
                                              let uu____83361 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____83392,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____83413) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____83472 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____83472 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____83361
                                                (fun uu____83544  ->
                                                   match uu____83544 with
                                                   | (wprobs,wl2) ->
                                                       let uu____83581 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____83581
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____83602
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____83602
                                                              then
                                                                let uu____83607
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____83609
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____83607
                                                                  uu____83609
                                                              else ());
                                                             (let uu____83615
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____83615
                                                                (fun
                                                                   uu____83651
                                                                    ->
                                                                   match uu____83651
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
                    | uu____83780 -> FStar_Pervasives_Native.None  in
                  let uu____83821 = solve_branches wl brs1 brs2  in
                  (match uu____83821 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____83872 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____83872 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____83906 =
                                FStar_List.map
                                  (fun uu____83918  ->
                                     match uu____83918 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____83906  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____83927 =
                              let uu____83928 =
                                let uu____83929 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____83929
                                  (let uu___3909_83937 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_83937.attempting);
                                     wl_deferred =
                                       (uu___3909_83937.wl_deferred);
                                     ctr = (uu___3909_83937.ctr);
                                     defer_ok = (uu___3909_83937.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_83937.umax_heuristic_ok);
                                     tcenv = (uu___3909_83937.tcenv);
                                     wl_implicits =
                                       (uu___3909_83937.wl_implicits)
                                   })
                                 in
                              solve env uu____83928  in
                            (match uu____83927 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____83942 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____83949,uu____83950) ->
                  let head1 =
                    let uu____83974 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____83974
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84020 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84020
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84066 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84066
                    then
                      let uu____84070 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84072 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84074 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84070 uu____84072 uu____84074
                    else ());
                   (let no_free_uvars t =
                      (let uu____84088 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84088) &&
                        (let uu____84092 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84092)
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
                      let uu____84109 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84109 = FStar_Syntax_Util.Equal  in
                    let uu____84110 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84110
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84114 = equal t1 t2  in
                         (if uu____84114
                          then
                            let uu____84117 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84117
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84122 =
                            let uu____84129 = equal t1 t2  in
                            if uu____84129
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84142 = mk_eq2 wl env orig t1 t2  in
                               match uu____84142 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84122 with
                          | (guard,wl1) ->
                              let uu____84163 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84163))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____84166,uu____84167) ->
                  let head1 =
                    let uu____84175 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84175
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84221 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84221
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84267 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84267
                    then
                      let uu____84271 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84273 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84275 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84271 uu____84273 uu____84275
                    else ());
                   (let no_free_uvars t =
                      (let uu____84289 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84289) &&
                        (let uu____84293 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84293)
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
                      let uu____84310 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84310 = FStar_Syntax_Util.Equal  in
                    let uu____84311 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84311
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84315 = equal t1 t2  in
                         (if uu____84315
                          then
                            let uu____84318 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84318
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84323 =
                            let uu____84330 = equal t1 t2  in
                            if uu____84330
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84343 = mk_eq2 wl env orig t1 t2  in
                               match uu____84343 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84323 with
                          | (guard,wl1) ->
                              let uu____84364 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84364))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____84367,uu____84368) ->
                  let head1 =
                    let uu____84370 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84370
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84416 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84416
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84462 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84462
                    then
                      let uu____84466 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84468 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84470 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84466 uu____84468 uu____84470
                    else ());
                   (let no_free_uvars t =
                      (let uu____84484 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84484) &&
                        (let uu____84488 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84488)
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
                      let uu____84505 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84505 = FStar_Syntax_Util.Equal  in
                    let uu____84506 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84506
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84510 = equal t1 t2  in
                         (if uu____84510
                          then
                            let uu____84513 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84513
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84518 =
                            let uu____84525 = equal t1 t2  in
                            if uu____84525
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84538 = mk_eq2 wl env orig t1 t2  in
                               match uu____84538 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84518 with
                          | (guard,wl1) ->
                              let uu____84559 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84559))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____84562,uu____84563) ->
                  let head1 =
                    let uu____84565 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84565
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84611 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84611
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84657 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84657
                    then
                      let uu____84661 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84663 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84665 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84661 uu____84663 uu____84665
                    else ());
                   (let no_free_uvars t =
                      (let uu____84679 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84679) &&
                        (let uu____84683 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84683)
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
                      let uu____84700 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84700 = FStar_Syntax_Util.Equal  in
                    let uu____84701 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84701
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84705 = equal t1 t2  in
                         (if uu____84705
                          then
                            let uu____84708 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84708
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84713 =
                            let uu____84720 = equal t1 t2  in
                            if uu____84720
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84733 = mk_eq2 wl env orig t1 t2  in
                               match uu____84733 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84713 with
                          | (guard,wl1) ->
                              let uu____84754 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84754))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____84757,uu____84758) ->
                  let head1 =
                    let uu____84760 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84760
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____84806 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____84806
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____84852 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____84852
                    then
                      let uu____84856 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____84858 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____84860 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____84856 uu____84858 uu____84860
                    else ());
                   (let no_free_uvars t =
                      (let uu____84874 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____84874) &&
                        (let uu____84878 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____84878)
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
                      let uu____84895 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____84895 = FStar_Syntax_Util.Equal  in
                    let uu____84896 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____84896
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____84900 = equal t1 t2  in
                         (if uu____84900
                          then
                            let uu____84903 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____84903
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____84908 =
                            let uu____84915 = equal t1 t2  in
                            if uu____84915
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____84928 = mk_eq2 wl env orig t1 t2  in
                               match uu____84928 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____84908 with
                          | (guard,wl1) ->
                              let uu____84949 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____84949))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____84952,uu____84953) ->
                  let head1 =
                    let uu____84971 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____84971
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85017 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85017
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85063 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85063
                    then
                      let uu____85067 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85069 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85071 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85067 uu____85069 uu____85071
                    else ());
                   (let no_free_uvars t =
                      (let uu____85085 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85085) &&
                        (let uu____85089 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85089)
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
                      let uu____85106 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85106 = FStar_Syntax_Util.Equal  in
                    let uu____85107 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85107
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85111 = equal t1 t2  in
                         (if uu____85111
                          then
                            let uu____85114 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85114
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85119 =
                            let uu____85126 = equal t1 t2  in
                            if uu____85126
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85139 = mk_eq2 wl env orig t1 t2  in
                               match uu____85139 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85119 with
                          | (guard,wl1) ->
                              let uu____85160 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85160))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85163,FStar_Syntax_Syntax.Tm_match uu____85164) ->
                  let head1 =
                    let uu____85188 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85188
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85234 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85234
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85280 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85280
                    then
                      let uu____85284 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85286 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85288 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85284 uu____85286 uu____85288
                    else ());
                   (let no_free_uvars t =
                      (let uu____85302 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85302) &&
                        (let uu____85306 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85306)
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
                      let uu____85323 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85323 = FStar_Syntax_Util.Equal  in
                    let uu____85324 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85324
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85328 = equal t1 t2  in
                         (if uu____85328
                          then
                            let uu____85331 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85331
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85336 =
                            let uu____85343 = equal t1 t2  in
                            if uu____85343
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85356 = mk_eq2 wl env orig t1 t2  in
                               match uu____85356 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85336 with
                          | (guard,wl1) ->
                              let uu____85377 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85377))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85380,FStar_Syntax_Syntax.Tm_uinst uu____85381) ->
                  let head1 =
                    let uu____85389 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85389
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85429 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85429
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85469 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85469
                    then
                      let uu____85473 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85475 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85477 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85473 uu____85475 uu____85477
                    else ());
                   (let no_free_uvars t =
                      (let uu____85491 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85491) &&
                        (let uu____85495 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85495)
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
                      let uu____85512 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85512 = FStar_Syntax_Util.Equal  in
                    let uu____85513 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85513
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85517 = equal t1 t2  in
                         (if uu____85517
                          then
                            let uu____85520 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85520
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85525 =
                            let uu____85532 = equal t1 t2  in
                            if uu____85532
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85545 = mk_eq2 wl env orig t1 t2  in
                               match uu____85545 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85525 with
                          | (guard,wl1) ->
                              let uu____85566 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85566))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85569,FStar_Syntax_Syntax.Tm_name uu____85570) ->
                  let head1 =
                    let uu____85572 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85572
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85612 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85612
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85652 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85652
                    then
                      let uu____85656 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85658 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85660 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85656 uu____85658 uu____85660
                    else ());
                   (let no_free_uvars t =
                      (let uu____85674 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85674) &&
                        (let uu____85678 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85678)
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
                      let uu____85695 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85695 = FStar_Syntax_Util.Equal  in
                    let uu____85696 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85696
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85700 = equal t1 t2  in
                         (if uu____85700
                          then
                            let uu____85703 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85703
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85708 =
                            let uu____85715 = equal t1 t2  in
                            if uu____85715
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85728 = mk_eq2 wl env orig t1 t2  in
                               match uu____85728 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85708 with
                          | (guard,wl1) ->
                              let uu____85749 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85749))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85752,FStar_Syntax_Syntax.Tm_constant uu____85753) ->
                  let head1 =
                    let uu____85755 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85755
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85795 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85795
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____85835 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____85835
                    then
                      let uu____85839 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____85841 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____85843 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____85839 uu____85841 uu____85843
                    else ());
                   (let no_free_uvars t =
                      (let uu____85857 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____85857) &&
                        (let uu____85861 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____85861)
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
                      let uu____85878 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____85878 = FStar_Syntax_Util.Equal  in
                    let uu____85879 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____85879
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____85883 = equal t1 t2  in
                         (if uu____85883
                          then
                            let uu____85886 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____85886
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____85891 =
                            let uu____85898 = equal t1 t2  in
                            if uu____85898
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____85911 = mk_eq2 wl env orig t1 t2  in
                               match uu____85911 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____85891 with
                          | (guard,wl1) ->
                              let uu____85932 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____85932))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____85935,FStar_Syntax_Syntax.Tm_fvar uu____85936) ->
                  let head1 =
                    let uu____85938 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____85938
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____85978 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____85978
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86018 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86018
                    then
                      let uu____86022 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86024 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86026 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86022 uu____86024 uu____86026
                    else ());
                   (let no_free_uvars t =
                      (let uu____86040 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86040) &&
                        (let uu____86044 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86044)
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
                      let uu____86061 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86061 = FStar_Syntax_Util.Equal  in
                    let uu____86062 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86062
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86066 = equal t1 t2  in
                         (if uu____86066
                          then
                            let uu____86069 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86069
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86074 =
                            let uu____86081 = equal t1 t2  in
                            if uu____86081
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86094 = mk_eq2 wl env orig t1 t2  in
                               match uu____86094 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86074 with
                          | (guard,wl1) ->
                              let uu____86115 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86115))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____86118,FStar_Syntax_Syntax.Tm_app uu____86119) ->
                  let head1 =
                    let uu____86137 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____86137
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____86177 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____86177
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____86217 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____86217
                    then
                      let uu____86221 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____86223 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____86225 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____86221 uu____86223 uu____86225
                    else ());
                   (let no_free_uvars t =
                      (let uu____86239 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____86239) &&
                        (let uu____86243 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____86243)
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
                      let uu____86260 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____86260 = FStar_Syntax_Util.Equal  in
                    let uu____86261 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____86261
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____86265 = equal t1 t2  in
                         (if uu____86265
                          then
                            let uu____86268 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____86268
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____86273 =
                            let uu____86280 = equal t1 t2  in
                            if uu____86280
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____86293 = mk_eq2 wl env orig t1 t2  in
                               match uu____86293 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____86273 with
                          | (guard,wl1) ->
                              let uu____86314 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____86314))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____86317,FStar_Syntax_Syntax.Tm_let uu____86318) ->
                  let uu____86345 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____86345
                  then
                    let uu____86348 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____86348
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____86352,uu____86353) ->
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
              | (uu____86385,FStar_Syntax_Syntax.Tm_let uu____86386) ->
                  let uu____86400 =
                    let uu____86406 =
                      let uu____86408 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____86410 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____86412 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____86414 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____86408 uu____86410 uu____86412 uu____86414
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____86406)
                     in
                  FStar_Errors.raise_error uu____86400
                    t1.FStar_Syntax_Syntax.pos
              | uu____86418 -> giveup env "head tag mismatch" orig))))

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
          (let uu____86482 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____86482
           then
             let uu____86487 =
               let uu____86489 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____86489  in
             let uu____86490 =
               let uu____86492 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____86492  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____86487 uu____86490
           else ());
          (let uu____86496 =
             let uu____86498 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____86498  in
           if uu____86496
           then
             let uu____86501 =
               let uu____86503 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____86505 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____86503 uu____86505
                in
             giveup env uu____86501 orig
           else
             (let uu____86510 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____86510 with
              | (ret_sub_prob,wl1) ->
                  let uu____86518 =
                    FStar_List.fold_right2
                      (fun uu____86555  ->
                         fun uu____86556  ->
                           fun uu____86557  ->
                             match (uu____86555, uu____86556, uu____86557)
                             with
                             | ((a1,uu____86601),(a2,uu____86603),(arg_sub_probs,wl2))
                                 ->
                                 let uu____86636 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____86636 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____86518 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____86666 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____86666  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____86674 = attempt sub_probs wl3  in
                       solve env uu____86674)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____86697 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____86700)::[] -> wp1
              | uu____86725 ->
                  let uu____86736 =
                    let uu____86738 =
                      let uu____86740 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____86740  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____86738
                     in
                  failwith uu____86736
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____86747 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____86747]
              | x -> x  in
            let uu____86749 =
              let uu____86760 =
                let uu____86769 =
                  let uu____86770 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____86770 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____86769  in
              [uu____86760]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____86749;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____86788 = lift_c1 ()  in solve_eq uu____86788 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_86797  ->
                       match uu___616_86797 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____86802 -> false))
                in
             let uu____86804 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____86834)::uu____86835,(wp2,uu____86837)::uu____86838)
                   -> (wp1, wp2)
               | uu____86911 ->
                   let uu____86936 =
                     let uu____86942 =
                       let uu____86944 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____86946 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____86944 uu____86946
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____86942)
                      in
                   FStar_Errors.raise_error uu____86936
                     env.FStar_TypeChecker_Env.range
                in
             match uu____86804 with
             | (wpc1,wpc2) ->
                 let uu____86956 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____86956
                 then
                   let uu____86961 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____86961 wl
                 else
                   (let uu____86965 =
                      let uu____86972 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____86972  in
                    match uu____86965 with
                    | (c2_decl,qualifiers) ->
                        let uu____86993 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____86993
                        then
                          let c1_repr =
                            let uu____87000 =
                              let uu____87001 =
                                let uu____87002 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____87002  in
                              let uu____87003 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____87001 uu____87003
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____87000
                             in
                          let c2_repr =
                            let uu____87005 =
                              let uu____87006 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____87007 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____87006 uu____87007
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____87005
                             in
                          let uu____87008 =
                            let uu____87013 =
                              let uu____87015 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____87017 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____87015 uu____87017
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____87013
                             in
                          (match uu____87008 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____87023 = attempt [prob] wl2  in
                               solve env uu____87023)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____87038 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____87038
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____87047 =
                                     let uu____87054 =
                                       let uu____87055 =
                                         let uu____87072 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____87075 =
                                           let uu____87086 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____87095 =
                                             let uu____87106 =
                                               let uu____87115 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____87115
                                                in
                                             [uu____87106]  in
                                           uu____87086 :: uu____87095  in
                                         (uu____87072, uu____87075)  in
                                       FStar_Syntax_Syntax.Tm_app uu____87055
                                        in
                                     FStar_Syntax_Syntax.mk uu____87054  in
                                   uu____87047 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____87164 =
                                    let uu____87171 =
                                      let uu____87172 =
                                        let uu____87189 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____87192 =
                                          let uu____87203 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____87212 =
                                            let uu____87223 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____87232 =
                                              let uu____87243 =
                                                let uu____87252 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____87252
                                                 in
                                              [uu____87243]  in
                                            uu____87223 :: uu____87232  in
                                          uu____87203 :: uu____87212  in
                                        (uu____87189, uu____87192)  in
                                      FStar_Syntax_Syntax.Tm_app uu____87172
                                       in
                                    FStar_Syntax_Syntax.mk uu____87171  in
                                  uu____87164 FStar_Pervasives_Native.None r)
                              in
                           (let uu____87306 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87306
                            then
                              let uu____87311 =
                                let uu____87313 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____87313
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____87311
                            else ());
                           (let uu____87317 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____87317 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____87326 =
                                    let uu____87329 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _87332  ->
                                         FStar_Pervasives_Native.Some _87332)
                                      uu____87329
                                     in
                                  solve_prob orig uu____87326 [] wl1  in
                                let uu____87333 = attempt [base_prob] wl2  in
                                solve env uu____87333))))
           in
        let uu____87334 = FStar_Util.physical_equality c1 c2  in
        if uu____87334
        then
          let uu____87337 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____87337
        else
          ((let uu____87341 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____87341
            then
              let uu____87346 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____87348 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____87346
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____87348
            else ());
           (let uu____87353 =
              let uu____87362 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____87365 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____87362, uu____87365)  in
            match uu____87353 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87383),FStar_Syntax_Syntax.Total
                    (t2,uu____87385)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____87402 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87402 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87404,FStar_Syntax_Syntax.Total uu____87405) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87424),FStar_Syntax_Syntax.Total
                    (t2,uu____87426)) ->
                     let uu____87443 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87443 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____87446),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87448)) ->
                     let uu____87465 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87465 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____87468),FStar_Syntax_Syntax.GTotal
                    (t2,uu____87470)) ->
                     let uu____87487 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____87487 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____87489,FStar_Syntax_Syntax.Comp uu____87490) ->
                     let uu____87499 =
                       let uu___4158_87502 = problem  in
                       let uu____87505 =
                         let uu____87506 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87506
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87502.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87505;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87502.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87502.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87502.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87502.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87502.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87502.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87502.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87502.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87499 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____87507,FStar_Syntax_Syntax.Comp uu____87508) ->
                     let uu____87517 =
                       let uu___4158_87520 = problem  in
                       let uu____87523 =
                         let uu____87524 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87524
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_87520.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____87523;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_87520.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_87520.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_87520.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_87520.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_87520.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_87520.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_87520.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_87520.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87517 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87525,FStar_Syntax_Syntax.GTotal uu____87526) ->
                     let uu____87535 =
                       let uu___4170_87538 = problem  in
                       let uu____87541 =
                         let uu____87542 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87542
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87538.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87538.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87538.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87541;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87538.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87538.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87538.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87538.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87538.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87538.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87535 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87543,FStar_Syntax_Syntax.Total uu____87544) ->
                     let uu____87553 =
                       let uu___4170_87556 = problem  in
                       let uu____87559 =
                         let uu____87560 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____87560
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_87556.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_87556.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_87556.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____87559;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_87556.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_87556.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_87556.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_87556.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_87556.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_87556.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____87553 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____87561,FStar_Syntax_Syntax.Comp uu____87562) ->
                     let uu____87563 =
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
                     if uu____87563
                     then
                       let uu____87566 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____87566 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____87573 =
                            let uu____87578 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____87578
                            then (c1_comp, c2_comp)
                            else
                              (let uu____87587 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____87588 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____87587, uu____87588))
                             in
                          match uu____87573 with
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
                           (let uu____87596 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____87596
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____87604 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____87604 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____87607 =
                                  let uu____87609 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____87611 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____87609 uu____87611
                                   in
                                giveup env uu____87607 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____87622 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____87622 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____87672 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____87672 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____87697 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____87728  ->
                match uu____87728 with
                | (u1,u2) ->
                    let uu____87736 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____87738 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____87736 uu____87738))
         in
      FStar_All.pipe_right uu____87697 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____87775,[])) when
          let uu____87802 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____87802 -> "{}"
      | uu____87805 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____87832 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____87832
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____87844 =
              FStar_List.map
                (fun uu____87857  ->
                   match uu____87857 with
                   | (uu____87864,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____87844 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____87875 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____87875 imps
  
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
                  let uu____87932 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____87932
                  then
                    let uu____87940 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____87942 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____87940
                      (rel_to_string rel) uu____87942
                  else "TOP"  in
                let uu____87948 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____87948 with
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
              let uu____88008 =
                let uu____88011 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _88014  -> FStar_Pervasives_Native.Some _88014)
                  uu____88011
                 in
              FStar_Syntax_Syntax.new_bv uu____88008 t1  in
            let uu____88015 =
              let uu____88020 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____88020
               in
            match uu____88015 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____88080 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____88080
         then
           let uu____88085 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____88085
         else ());
        (let uu____88092 =
           FStar_Util.record_time (fun uu____88099  -> solve env probs)  in
         match uu____88092 with
         | (sol,ms) ->
             ((let uu____88111 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____88111
               then
                 let uu____88116 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____88116
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____88129 =
                     FStar_Util.record_time
                       (fun uu____88136  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____88129 with
                    | ((),ms1) ->
                        ((let uu____88147 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____88147
                          then
                            let uu____88152 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____88152
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____88166 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____88166
                     then
                       let uu____88173 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____88173
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
          ((let uu____88200 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____88200
            then
              let uu____88205 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____88205
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____88212 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____88212
             then
               let uu____88217 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____88217
             else ());
            (let f2 =
               let uu____88223 =
                 let uu____88224 = FStar_Syntax_Util.unmeta f1  in
                 uu____88224.FStar_Syntax_Syntax.n  in
               match uu____88223 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____88228 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_88229 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_88229.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_88229.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_88229.FStar_TypeChecker_Env.implicits)
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
            let uu____88284 =
              let uu____88285 =
                let uu____88286 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _88287  ->
                       FStar_TypeChecker_Common.NonTrivial _88287)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____88286;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____88285  in
            FStar_All.pipe_left
              (fun _88294  -> FStar_Pervasives_Native.Some _88294)
              uu____88284
  
let with_guard_no_simp :
  'Auu____88304 .
    'Auu____88304 ->
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
            let uu____88327 =
              let uu____88328 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _88329  -> FStar_TypeChecker_Common.NonTrivial _88329)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____88328;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____88327
  
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
          (let uu____88362 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____88362
           then
             let uu____88367 = FStar_Syntax_Print.term_to_string t1  in
             let uu____88369 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____88367
               uu____88369
           else ());
          (let uu____88374 =
             let uu____88379 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____88379
              in
           match uu____88374 with
           | (prob,wl) ->
               let g =
                 let uu____88387 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____88397  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____88387  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____88433 = try_teq true env t1 t2  in
        match uu____88433 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____88438 = FStar_TypeChecker_Env.get_range env  in
              let uu____88439 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____88438 uu____88439);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____88447 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____88447
              then
                let uu____88452 = FStar_Syntax_Print.term_to_string t1  in
                let uu____88454 = FStar_Syntax_Print.term_to_string t2  in
                let uu____88456 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____88452
                  uu____88454 uu____88456
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
          let uu____88482 = FStar_TypeChecker_Env.get_range env  in
          let uu____88483 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____88482 uu____88483
  
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
        (let uu____88512 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____88512
         then
           let uu____88517 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____88519 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____88517 uu____88519
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____88530 =
           let uu____88537 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____88537 "sub_comp"
            in
         match uu____88530 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____88550 =
                 FStar_Util.record_time
                   (fun uu____88562  ->
                      let uu____88563 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____88574  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____88563)
                  in
               match uu____88550 with
               | (r,ms) ->
                   ((let uu____88605 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____88605
                     then
                       let uu____88610 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____88612 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____88614 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____88610 uu____88612
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____88614
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
      fun uu____88652  ->
        match uu____88652 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____88695 =
                 let uu____88701 =
                   let uu____88703 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____88705 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____88703 uu____88705
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____88701)  in
               let uu____88709 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____88695 uu____88709)
               in
            let equiv1 v1 v' =
              let uu____88722 =
                let uu____88727 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____88728 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____88727, uu____88728)  in
              match uu____88722 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____88748 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____88779 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____88779 with
                      | FStar_Syntax_Syntax.U_unif uu____88786 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____88815  ->
                                    match uu____88815 with
                                    | (u,v') ->
                                        let uu____88824 = equiv1 v1 v'  in
                                        if uu____88824
                                        then
                                          let uu____88829 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____88829 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____88850 -> []))
               in
            let uu____88855 =
              let wl =
                let uu___4377_88859 = empty_worklist env  in
                {
                  attempting = (uu___4377_88859.attempting);
                  wl_deferred = (uu___4377_88859.wl_deferred);
                  ctr = (uu___4377_88859.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_88859.smt_ok);
                  umax_heuristic_ok = (uu___4377_88859.umax_heuristic_ok);
                  tcenv = (uu___4377_88859.tcenv);
                  wl_implicits = (uu___4377_88859.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____88878  ->
                      match uu____88878 with
                      | (lb,v1) ->
                          let uu____88885 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____88885 with
                           | USolved wl1 -> ()
                           | uu____88888 -> fail1 lb v1)))
               in
            let rec check_ineq uu____88899 =
              match uu____88899 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____88911) -> true
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
                      uu____88935,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____88937,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____88948) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____88956,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____88965 -> false)
               in
            let uu____88971 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____88988  ->
                      match uu____88988 with
                      | (u,v1) ->
                          let uu____88996 = check_ineq (u, v1)  in
                          if uu____88996
                          then true
                          else
                            ((let uu____89004 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____89004
                              then
                                let uu____89009 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____89011 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____89009
                                  uu____89011
                              else ());
                             false)))
               in
            if uu____88971
            then ()
            else
              ((let uu____89021 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____89021
                then
                  ((let uu____89027 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____89027);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____89039 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____89039))
                else ());
               (let uu____89052 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____89052))
  
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
        let fail1 uu____89126 =
          match uu____89126 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_89152 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_89152.attempting);
            wl_deferred = (uu___4454_89152.wl_deferred);
            ctr = (uu___4454_89152.ctr);
            defer_ok;
            smt_ok = (uu___4454_89152.smt_ok);
            umax_heuristic_ok = (uu___4454_89152.umax_heuristic_ok);
            tcenv = (uu___4454_89152.tcenv);
            wl_implicits = (uu___4454_89152.wl_implicits)
          }  in
        (let uu____89155 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____89155
         then
           let uu____89160 = FStar_Util.string_of_bool defer_ok  in
           let uu____89162 = wl_to_string wl  in
           let uu____89164 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____89160 uu____89162 uu____89164
         else ());
        (let g1 =
           let uu____89170 = solve_and_commit env wl fail1  in
           match uu____89170 with
           | FStar_Pervasives_Native.Some
               (uu____89177::uu____89178,uu____89179) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_89208 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_89208.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_89208.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____89209 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_89218 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_89218.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_89218.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_89218.FStar_TypeChecker_Env.implicits)
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
    let uu____89261 = FStar_ST.op_Bang last_proof_ns  in
    match uu____89261 with
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
            let uu___4493_89386 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_89386.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_89386.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_89386.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____89387 =
            let uu____89389 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____89389  in
          if uu____89387
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____89401 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____89402 =
                       let uu____89404 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____89404
                        in
                     FStar_Errors.diag uu____89401 uu____89402)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____89412 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____89413 =
                        let uu____89415 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____89415
                         in
                      FStar_Errors.diag uu____89412 uu____89413)
                   else ();
                   (let uu____89421 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____89421
                      "discharge_guard'" env vc1);
                   (let uu____89423 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____89423 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____89432 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89433 =
                                let uu____89435 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____89435
                                 in
                              FStar_Errors.diag uu____89432 uu____89433)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____89445 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____89446 =
                                let uu____89448 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____89448
                                 in
                              FStar_Errors.diag uu____89445 uu____89446)
                           else ();
                           (let vcs =
                              let uu____89462 = FStar_Options.use_tactics ()
                                 in
                              if uu____89462
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____89484  ->
                                     (let uu____89486 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____89486);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____89530  ->
                                              match uu____89530 with
                                              | (env1,goal,opts) ->
                                                  let uu____89546 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____89546, opts)))))
                              else
                                (let uu____89549 =
                                   let uu____89556 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____89556)  in
                                 [uu____89549])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____89589  ->
                                    match uu____89589 with
                                    | (env1,goal,opts) ->
                                        let uu____89599 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____89599 with
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
                                                (let uu____89611 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89612 =
                                                   let uu____89614 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____89616 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____89614 uu____89616
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89611 uu____89612)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____89623 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____89624 =
                                                   let uu____89626 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____89626
                                                    in
                                                 FStar_Errors.diag
                                                   uu____89623 uu____89624)
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
      let uu____89644 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____89644 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____89653 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____89653
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____89667 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____89667 with
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
        let uu____89697 = try_teq false env t1 t2  in
        match uu____89697 with
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
            let uu____89741 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____89741 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____89754 ->
                     let uu____89767 =
                       let uu____89768 = FStar_Syntax_Subst.compress r  in
                       uu____89768.FStar_Syntax_Syntax.n  in
                     (match uu____89767 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____89773) ->
                          unresolved ctx_u'
                      | uu____89790 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____89814 = acc  in
            match uu____89814 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____89833 = hd1  in
                     (match uu____89833 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____89844 = unresolved ctx_u  in
                             if uu____89844
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____89868 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____89868
                                     then
                                       let uu____89872 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____89872
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____89881 = teq_nosmt env1 t tm
                                          in
                                       match uu____89881 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_89891 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_89891.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_89891.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_89891.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_89891.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_89891.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_89891.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_89891.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_89899 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_89899.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_89899.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_89899.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_89910 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_89910.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_89910.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_89910.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_89910.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_89910.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_89910.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_89910.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_89910.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_89910.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_89910.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_89910.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_89910.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_89910.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_89910.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_89910.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_89910.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_89910.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_89910.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_89910.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_89910.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_89910.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_89910.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_89910.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_89910.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_89910.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_89910.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_89910.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_89910.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_89910.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_89910.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_89910.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_89910.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_89910.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_89910.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_89910.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_89910.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_89910.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_89910.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_89910.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_89910.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_89910.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_89910.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_89914 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_89914.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_89914.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_89914.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_89914.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_89914.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_89914.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_89914.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_89914.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_89914.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_89914.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_89914.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_89914.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_89914.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_89914.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_89914.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_89914.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_89914.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_89914.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_89914.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_89914.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_89914.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_89914.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_89914.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_89914.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_89914.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_89914.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_89914.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_89914.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_89914.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_89914.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_89914.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_89914.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_89914.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_89914.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_89914.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_89914.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_89914.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_89914.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_89914.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_89914.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_89914.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_89914.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____89919 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____89919
                                   then
                                     let uu____89924 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____89926 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____89928 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____89930 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____89924 uu____89926 uu____89928
                                       reason uu____89930
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_89937  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____89944 =
                                             let uu____89954 =
                                               let uu____89962 =
                                                 let uu____89964 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____89966 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____89968 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____89964 uu____89966
                                                   uu____89968
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____89962, r)
                                                in
                                             [uu____89954]  in
                                           FStar_Errors.add_errors
                                             uu____89944);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_89988 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_89988.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_89988.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_89988.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____89992 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____90003  ->
                                               let uu____90004 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____90006 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____90008 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____90004 uu____90006
                                                 reason uu____90008)) env2 g2
                                         true
                                        in
                                     match uu____89992 with
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
          let uu___4640_90016 = g  in
          let uu____90017 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_90016.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_90016.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_90016.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____90017
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
        let uu____90060 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____90060 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____90061 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____90061
      | imp::uu____90063 ->
          let uu____90066 =
            let uu____90072 =
              let uu____90074 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____90076 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____90074 uu____90076 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____90072)
             in
          FStar_Errors.raise_error uu____90066
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90098 = teq_nosmt env t1 t2  in
        match uu____90098 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_90117 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_90117.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_90117.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_90117.FStar_TypeChecker_Env.implicits)
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
        (let uu____90153 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90153
         then
           let uu____90158 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90160 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____90158
             uu____90160
         else ());
        (let uu____90165 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90165 with
         | (prob,x,wl) ->
             let g =
               let uu____90184 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____90195  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90184  in
             ((let uu____90216 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____90216
               then
                 let uu____90221 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____90223 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____90225 =
                   let uu____90227 = FStar_Util.must g  in
                   guard_to_string env uu____90227  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____90221 uu____90223 uu____90225
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
        let uu____90264 = check_subtyping env t1 t2  in
        match uu____90264 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90283 =
              let uu____90284 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____90284 g  in
            FStar_Pervasives_Native.Some uu____90283
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90303 = check_subtyping env t1 t2  in
        match uu____90303 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____90322 =
              let uu____90323 =
                let uu____90324 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____90324]  in
              FStar_TypeChecker_Env.close_guard env uu____90323 g  in
            FStar_Pervasives_Native.Some uu____90322
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____90362 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____90362
         then
           let uu____90367 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____90369 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____90367
             uu____90369
         else ());
        (let uu____90374 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____90374 with
         | (prob,x,wl) ->
             let g =
               let uu____90389 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____90400  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____90389  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____90424 =
                      let uu____90425 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____90425]  in
                    FStar_TypeChecker_Env.close_guard env uu____90424 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____90466 = subtype_nosmt env t1 t2  in
        match uu____90466 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  