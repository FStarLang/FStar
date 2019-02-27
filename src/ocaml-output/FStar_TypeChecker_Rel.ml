open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____65122 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____65158 -> false
  
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
                    let uu____65582 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____65582;
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
                     (let uu___656_65614 = wl  in
                      {
                        attempting = (uu___656_65614.attempting);
                        wl_deferred = (uu___656_65614.wl_deferred);
                        ctr = (uu___656_65614.ctr);
                        defer_ok = (uu___656_65614.defer_ok);
                        smt_ok = (uu___656_65614.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_65614.umax_heuristic_ok);
                        tcenv = (uu___656_65614.tcenv);
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
            let uu___662_65647 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_65647.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_65647.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_65647.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_65647.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_65647.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_65647.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_65647.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_65647.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_65647.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_65647.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_65647.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_65647.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_65647.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_65647.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_65647.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_65647.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_65647.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_65647.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_65647.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_65647.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_65647.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_65647.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_65647.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_65647.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_65647.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_65647.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_65647.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_65647.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_65647.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_65647.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_65647.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_65647.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_65647.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_65647.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_65647.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_65647.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_65647.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_65647.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_65647.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_65647.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_65647.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_65647.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____65649 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____65649 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____65692 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____65729 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____65763 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____65774 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____65785 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_65803  ->
    match uu___585_65803 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____65815 = FStar_Syntax_Util.head_and_args t  in
    match uu____65815 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____65878 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____65880 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____65895 =
                     let uu____65897 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____65897  in
                   FStar_Util.format1 "@<%s>" uu____65895
                in
             let uu____65901 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____65878 uu____65880 uu____65901
         | uu____65904 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_65916  ->
      match uu___586_65916 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____65921 =
            let uu____65925 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____65927 =
              let uu____65931 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____65933 =
                let uu____65937 =
                  let uu____65941 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____65941]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____65937
                 in
              uu____65931 :: uu____65933  in
            uu____65925 :: uu____65927  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____65921
      | FStar_TypeChecker_Common.CProb p ->
          let uu____65952 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____65954 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____65956 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____65952
            uu____65954 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____65956
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_65970  ->
      match uu___587_65970 with
      | UNIV (u,t) ->
          let x =
            let uu____65976 = FStar_Options.hide_uvar_nums ()  in
            if uu____65976
            then "?"
            else
              (let uu____65983 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____65983 FStar_Util.string_of_int)
             in
          let uu____65987 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____65987
      | TERM (u,t) ->
          let x =
            let uu____65994 = FStar_Options.hide_uvar_nums ()  in
            if uu____65994
            then "?"
            else
              (let uu____66001 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____66001 FStar_Util.string_of_int)
             in
          let uu____66005 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____66005
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____66024 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____66024 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____66045 =
      let uu____66049 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____66049
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____66045 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____66068 .
    (FStar_Syntax_Syntax.term * 'Auu____66068) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____66087 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____66108  ->
              match uu____66108 with
              | (x,uu____66115) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____66087 (FStar_String.concat " ")
  
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
        (let uu____66158 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____66158
         then
           let uu____66163 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____66163
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_66174  ->
    match uu___588_66174 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____66180 .
    'Auu____66180 FStar_TypeChecker_Common.problem ->
      'Auu____66180 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_66192 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_66192.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_66192.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_66192.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_66192.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_66192.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_66192.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_66192.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____66200 .
    'Auu____66200 FStar_TypeChecker_Common.problem ->
      'Auu____66200 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_66220  ->
    match uu___589_66220 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66226  -> FStar_TypeChecker_Common.TProb _66226)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66232  -> FStar_TypeChecker_Common.CProb _66232)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_66238  ->
    match uu___590_66238 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_66244 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_66244.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_66244.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_66244.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_66244.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_66244.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_66244.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_66244.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_66244.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_66244.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_66252 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_66252.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_66252.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_66252.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_66252.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_66252.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_66252.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_66252.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_66252.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_66252.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_66265  ->
      match uu___591_66265 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_66272  ->
    match uu___592_66272 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_66285  ->
    match uu___593_66285 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_66300  ->
    match uu___594_66300 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_66315  ->
    match uu___595_66315 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_66329  ->
    match uu___596_66329 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_66343  ->
    match uu___597_66343 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_66355  ->
    match uu___598_66355 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____66371 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____66371) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____66401 =
          let uu____66403 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66403  in
        if uu____66401
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____66440)::bs ->
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
          let uu____66487 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66511 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66511]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66487
      | FStar_TypeChecker_Common.CProb p ->
          let uu____66539 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66563 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66563]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66539
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____66610 =
          let uu____66612 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66612  in
        if uu____66610
        then ()
        else
          (let uu____66617 =
             let uu____66620 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____66620
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____66617 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____66669 =
          let uu____66671 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66671  in
        if uu____66669
        then ()
        else
          (let uu____66676 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____66676)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____66696 =
        let uu____66698 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____66698  in
      if uu____66696
      then ()
      else
        (let msgf m =
           let uu____66712 =
             let uu____66714 =
               let uu____66716 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____66716 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____66714  in
           Prims.op_Hat msg uu____66712  in
         (let uu____66721 = msgf "scope"  in
          let uu____66724 = p_scope prob  in
          def_scope_wf uu____66721 (p_loc prob) uu____66724);
         (let uu____66736 = msgf "guard"  in
          def_check_scoped uu____66736 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____66743 = msgf "lhs"  in
                def_check_scoped uu____66743 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66746 = msgf "rhs"  in
                def_check_scoped uu____66746 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____66753 = msgf "lhs"  in
                def_check_scoped_comp uu____66753 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66756 = msgf "rhs"  in
                def_check_scoped_comp uu____66756 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_66777 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_66777.wl_deferred);
          ctr = (uu___831_66777.ctr);
          defer_ok = (uu___831_66777.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_66777.umax_heuristic_ok);
          tcenv = (uu___831_66777.tcenv);
          wl_implicits = (uu___831_66777.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____66785 .
    FStar_TypeChecker_Env.env ->
      ('Auu____66785 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_66808 = empty_worklist env  in
      let uu____66809 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____66809;
        wl_deferred = (uu___835_66808.wl_deferred);
        ctr = (uu___835_66808.ctr);
        defer_ok = (uu___835_66808.defer_ok);
        smt_ok = (uu___835_66808.smt_ok);
        umax_heuristic_ok = (uu___835_66808.umax_heuristic_ok);
        tcenv = (uu___835_66808.tcenv);
        wl_implicits = (uu___835_66808.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_66832 = wl  in
        {
          attempting = (uu___840_66832.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_66832.ctr);
          defer_ok = (uu___840_66832.defer_ok);
          smt_ok = (uu___840_66832.smt_ok);
          umax_heuristic_ok = (uu___840_66832.umax_heuristic_ok);
          tcenv = (uu___840_66832.tcenv);
          wl_implicits = (uu___840_66832.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_66860 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_66860.wl_deferred);
         ctr = (uu___845_66860.ctr);
         defer_ok = (uu___845_66860.defer_ok);
         smt_ok = (uu___845_66860.smt_ok);
         umax_heuristic_ok = (uu___845_66860.umax_heuristic_ok);
         tcenv = (uu___845_66860.tcenv);
         wl_implicits = (uu___845_66860.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____66874 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____66874 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____66908 = FStar_Syntax_Util.type_u ()  in
            match uu____66908 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____66920 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____66920 with
                 | (uu____66938,tt,wl1) ->
                     let uu____66941 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____66941, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_66947  ->
    match uu___599_66947 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _66953  -> FStar_TypeChecker_Common.TProb _66953) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _66959  -> FStar_TypeChecker_Common.CProb _66959) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____66967 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____66967 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____66987  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____67084 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____67084 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____67084 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____67084 FStar_TypeChecker_Common.problem *
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
                        let uu____67171 =
                          let uu____67180 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67180]  in
                        FStar_List.append scope uu____67171
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____67223 =
                      let uu____67226 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____67226  in
                    FStar_List.append uu____67223
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____67245 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67245 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____67271 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67271;
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
                  (let uu____67345 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67345 with
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
                  (let uu____67433 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67433 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____67471 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____67471 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____67471 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____67471 FStar_TypeChecker_Common.problem *
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
                          let uu____67539 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67539]  in
                        let uu____67558 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____67558
                     in
                  let uu____67561 =
                    let uu____67568 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_67579 = wl  in
                       {
                         attempting = (uu___928_67579.attempting);
                         wl_deferred = (uu___928_67579.wl_deferred);
                         ctr = (uu___928_67579.ctr);
                         defer_ok = (uu___928_67579.defer_ok);
                         smt_ok = (uu___928_67579.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_67579.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_67579.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____67568
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67561 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____67597 =
                              let uu____67602 =
                                let uu____67603 =
                                  let uu____67612 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____67612
                                   in
                                [uu____67603]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____67602
                               in
                            uu____67597 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____67642 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67642;
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
                let uu____67690 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____67690;
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
  'Auu____67705 .
    worklist ->
      'Auu____67705 FStar_TypeChecker_Common.problem ->
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
              let uu____67738 =
                let uu____67741 =
                  let uu____67742 =
                    let uu____67749 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____67749)  in
                  FStar_Syntax_Syntax.NT uu____67742  in
                [uu____67741]  in
              FStar_Syntax_Subst.subst uu____67738 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____67773 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____67773
        then
          let uu____67781 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____67784 = prob_to_string env d  in
          let uu____67786 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____67781 uu____67784 uu____67786 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____67802 -> failwith "impossible"  in
           let uu____67805 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____67821 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67823 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67821, uu____67823)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____67830 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67832 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67830, uu____67832)
              in
           match uu____67805 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_67860  ->
            match uu___600_67860 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____67872 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____67876 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____67876 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_67907  ->
           match uu___601_67907 with
           | UNIV uu____67910 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____67917 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____67917
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
        (fun uu___602_67945  ->
           match uu___602_67945 with
           | UNIV (u',t) ->
               let uu____67950 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____67950
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____67957 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67969 =
        let uu____67970 =
          let uu____67971 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____67971
           in
        FStar_Syntax_Subst.compress uu____67970  in
      FStar_All.pipe_right uu____67969 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67983 =
        let uu____67984 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____67984  in
      FStar_All.pipe_right uu____67983 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67992 = FStar_Syntax_Util.head_and_args t  in
    match uu____67992 with
    | (h,uu____68011) ->
        let uu____68036 =
          let uu____68037 = FStar_Syntax_Subst.compress h  in
          uu____68037.FStar_Syntax_Syntax.n  in
        (match uu____68036 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____68042 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____68055 = should_strongly_reduce t  in
      if uu____68055
      then
        let uu____68058 =
          let uu____68059 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____68059  in
        FStar_All.pipe_right uu____68058 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____68069 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____68069) ->
        (FStar_Syntax_Syntax.term * 'Auu____68069)
  =
  fun env  ->
    fun t  ->
      let uu____68092 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____68092, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____68144  ->
              match uu____68144 with
              | (x,imp) ->
                  let uu____68163 =
                    let uu___1025_68164 = x  in
                    let uu____68165 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_68164.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_68164.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____68165
                    }  in
                  (uu____68163, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____68189 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____68189
        | FStar_Syntax_Syntax.U_max us ->
            let uu____68193 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____68193
        | uu____68196 -> u2  in
      let uu____68197 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____68197
  
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
                (let uu____68318 = norm_refinement env t12  in
                 match uu____68318 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____68333;
                     FStar_Syntax_Syntax.vars = uu____68334;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____68358 =
                       let uu____68360 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____68362 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____68360 uu____68362
                        in
                     failwith uu____68358)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____68378 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____68378
          | FStar_Syntax_Syntax.Tm_uinst uu____68379 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68416 =
                   let uu____68417 = FStar_Syntax_Subst.compress t1'  in
                   uu____68417.FStar_Syntax_Syntax.n  in
                 match uu____68416 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68432 -> aux true t1'
                 | uu____68440 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____68455 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68486 =
                   let uu____68487 = FStar_Syntax_Subst.compress t1'  in
                   uu____68487.FStar_Syntax_Syntax.n  in
                 match uu____68486 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68502 -> aux true t1'
                 | uu____68510 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____68525 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68572 =
                   let uu____68573 = FStar_Syntax_Subst.compress t1'  in
                   uu____68573.FStar_Syntax_Syntax.n  in
                 match uu____68572 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68588 -> aux true t1'
                 | uu____68596 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____68611 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____68626 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____68641 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____68656 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____68671 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____68700 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____68733 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____68754 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____68781 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____68809 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____68846 ->
              let uu____68853 =
                let uu____68855 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68857 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68855 uu____68857
                 in
              failwith uu____68853
          | FStar_Syntax_Syntax.Tm_ascribed uu____68872 ->
              let uu____68899 =
                let uu____68901 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68903 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68901 uu____68903
                 in
              failwith uu____68899
          | FStar_Syntax_Syntax.Tm_delayed uu____68918 ->
              let uu____68941 =
                let uu____68943 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68945 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68943 uu____68945
                 in
              failwith uu____68941
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____68960 =
                let uu____68962 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68964 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68962 uu____68964
                 in
              failwith uu____68960
           in
        let uu____68979 = whnf env t1  in aux false uu____68979
  
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
      let uu____69040 = base_and_refinement env t  in
      FStar_All.pipe_right uu____69040 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____69081 = FStar_Syntax_Syntax.null_bv t  in
    (uu____69081, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____69108 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____69108 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____69168  ->
    match uu____69168 with
    | (t_base,refopt) ->
        let uu____69199 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____69199 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____69241 =
      let uu____69245 =
        let uu____69248 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____69275  ->
                  match uu____69275 with | (uu____69284,uu____69285,x) -> x))
           in
        FStar_List.append wl.attempting uu____69248  in
      FStar_List.map (wl_prob_to_string wl) uu____69245  in
    FStar_All.pipe_right uu____69241 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____69308 .
    ('Auu____69308 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____69320  ->
    match uu____69320 with
    | (uu____69327,c,args) ->
        let uu____69330 = print_ctx_uvar c  in
        let uu____69332 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____69330 uu____69332
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____69342 = FStar_Syntax_Util.head_and_args t  in
    match uu____69342 with
    | (head1,_args) ->
        let uu____69386 =
          let uu____69387 = FStar_Syntax_Subst.compress head1  in
          uu____69387.FStar_Syntax_Syntax.n  in
        (match uu____69386 with
         | FStar_Syntax_Syntax.Tm_uvar uu____69391 -> true
         | uu____69405 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____69413 = FStar_Syntax_Util.head_and_args t  in
    match uu____69413 with
    | (head1,_args) ->
        let uu____69456 =
          let uu____69457 = FStar_Syntax_Subst.compress head1  in
          uu____69457.FStar_Syntax_Syntax.n  in
        (match uu____69456 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____69461) -> u
         | uu____69478 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____69503 = FStar_Syntax_Util.head_and_args t  in
      match uu____69503 with
      | (head1,args) ->
          let uu____69550 =
            let uu____69551 = FStar_Syntax_Subst.compress head1  in
            uu____69551.FStar_Syntax_Syntax.n  in
          (match uu____69550 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____69559)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____69592 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_69617  ->
                         match uu___603_69617 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____69622 =
                               let uu____69623 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____69623.FStar_Syntax_Syntax.n  in
                             (match uu____69622 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____69628 -> false)
                         | uu____69630 -> true))
                  in
               (match uu____69592 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____69655 =
                        FStar_List.collect
                          (fun uu___604_69667  ->
                             match uu___604_69667 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____69671 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____69671]
                             | uu____69672 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____69655 FStar_List.rev  in
                    let uu____69695 =
                      let uu____69702 =
                        let uu____69711 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_69733  ->
                                  match uu___605_69733 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____69737 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____69737]
                                  | uu____69738 -> []))
                           in
                        FStar_All.pipe_right uu____69711 FStar_List.rev  in
                      let uu____69761 =
                        let uu____69764 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____69764  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____69702 uu____69761
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____69695 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____69800  ->
                                match uu____69800 with
                                | (x,i) ->
                                    let uu____69819 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____69819, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____69850  ->
                                match uu____69850 with
                                | (a,i) ->
                                    let uu____69869 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____69869, i)) args_sol
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
           | uu____69891 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____69913 =
          let uu____69936 =
            let uu____69937 = FStar_Syntax_Subst.compress k  in
            uu____69937.FStar_Syntax_Syntax.n  in
          match uu____69936 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____70019 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____70019)
              else
                (let uu____70054 = FStar_Syntax_Util.abs_formals t  in
                 match uu____70054 with
                 | (ys',t1,uu____70087) ->
                     let uu____70092 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____70092))
          | uu____70131 ->
              let uu____70132 =
                let uu____70137 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____70137)  in
              ((ys, t), uu____70132)
           in
        match uu____69913 with
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
                 let uu____70232 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____70232 c  in
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
               (let uu____70310 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70310
                then
                  let uu____70315 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____70317 = print_ctx_uvar uv  in
                  let uu____70319 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____70315 uu____70317 uu____70319
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____70328 =
                   let uu____70330 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____70330  in
                 let uu____70333 =
                   let uu____70336 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____70336
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____70328 uu____70333 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____70369 =
               let uu____70370 =
                 let uu____70372 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____70374 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____70372 uu____70374
                  in
               failwith uu____70370  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____70440  ->
                       match uu____70440 with
                       | (a,i) ->
                           let uu____70461 =
                             let uu____70462 = FStar_Syntax_Subst.compress a
                                in
                             uu____70462.FStar_Syntax_Syntax.n  in
                           (match uu____70461 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____70488 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____70498 =
                 let uu____70500 = is_flex g  in
                 Prims.op_Negation uu____70500  in
               if uu____70498
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____70509 = destruct_flex_t g wl  in
                  match uu____70509 with
                  | ((uu____70514,uv1,args),wl1) ->
                      ((let uu____70519 = args_as_binders args  in
                        assign_solution uu____70519 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_70521 = wl1  in
              {
                attempting = (uu___1277_70521.attempting);
                wl_deferred = (uu___1277_70521.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_70521.defer_ok);
                smt_ok = (uu___1277_70521.smt_ok);
                umax_heuristic_ok = (uu___1277_70521.umax_heuristic_ok);
                tcenv = (uu___1277_70521.tcenv);
                wl_implicits = (uu___1277_70521.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____70546 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____70546
         then
           let uu____70551 = FStar_Util.string_of_int pid  in
           let uu____70553 =
             let uu____70555 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____70555 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____70551
             uu____70553
         else ());
        commit sol;
        (let uu___1285_70569 = wl  in
         {
           attempting = (uu___1285_70569.attempting);
           wl_deferred = (uu___1285_70569.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_70569.defer_ok);
           smt_ok = (uu___1285_70569.smt_ok);
           umax_heuristic_ok = (uu___1285_70569.umax_heuristic_ok);
           tcenv = (uu___1285_70569.tcenv);
           wl_implicits = (uu___1285_70569.wl_implicits)
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
             | (uu____70635,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____70663 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____70663
              in
           (let uu____70669 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____70669
            then
              let uu____70674 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____70678 =
                let uu____70680 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____70680 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____70674
                uu____70678
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
        let uu____70715 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____70715 FStar_Util.set_elements  in
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
      let uu____70755 = occurs uk t  in
      match uu____70755 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____70794 =
                 let uu____70796 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____70798 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____70796 uu____70798
                  in
               FStar_Pervasives_Native.Some uu____70794)
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
            let uu____70918 = maximal_prefix bs_tail bs'_tail  in
            (match uu____70918 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____70969 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____71026  ->
             match uu____71026 with
             | (x,uu____71038) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____71056 = FStar_List.last bs  in
      match uu____71056 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____71080) ->
          let uu____71091 =
            FStar_Util.prefix_until
              (fun uu___606_71106  ->
                 match uu___606_71106 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____71109 -> false) g
             in
          (match uu____71091 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____71123,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____71160 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____71160 with
        | (pfx,uu____71170) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____71182 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____71182 with
             | (uu____71190,src',wl1) ->
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
                 | uu____71304 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____71305 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____71369  ->
                  fun uu____71370  ->
                    match (uu____71369, uu____71370) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____71473 =
                          let uu____71475 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____71475
                           in
                        if uu____71473
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____71509 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____71509
                           then
                             let uu____71526 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____71526)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____71305 with | (isect,uu____71576) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____71612 'Auu____71613 .
    (FStar_Syntax_Syntax.bv * 'Auu____71612) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____71613) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____71671  ->
              fun uu____71672  ->
                match (uu____71671, uu____71672) with
                | ((a,uu____71691),(b,uu____71693)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____71709 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____71709) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____71740  ->
           match uu____71740 with
           | (y,uu____71747) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____71757 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____71757) Prims.list ->
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
                   let uu____71919 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____71919
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____71952 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____72004 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____72049 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____72071 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_72079  ->
    match uu___607_72079 with
    | MisMatch (d1,d2) ->
        let uu____72091 =
          let uu____72093 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____72095 =
            let uu____72097 =
              let uu____72099 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____72099 ")"  in
            Prims.op_Hat ") (" uu____72097  in
          Prims.op_Hat uu____72093 uu____72095  in
        Prims.op_Hat "MisMatch (" uu____72091
    | HeadMatch u ->
        let uu____72106 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____72106
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_72115  ->
    match uu___608_72115 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____72132 -> HeadMatch false
  
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
          let uu____72154 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____72154 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____72165 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____72189 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____72199 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____72226 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____72226
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____72227 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____72228 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____72229 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____72242 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____72256 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____72280) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72286,uu____72287) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____72329) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____72354;
             FStar_Syntax_Syntax.index = uu____72355;
             FStar_Syntax_Syntax.sort = t2;_},uu____72357)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____72365 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____72366 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____72367 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____72382 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____72389 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____72409 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____72409
  
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
           { FStar_Syntax_Syntax.blob = uu____72428;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72429;
             FStar_Syntax_Syntax.ltyp = uu____72430;
             FStar_Syntax_Syntax.rng = uu____72431;_},uu____72432)
            ->
            let uu____72443 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____72443 t21
        | (uu____72444,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____72445;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72446;
             FStar_Syntax_Syntax.ltyp = uu____72447;
             FStar_Syntax_Syntax.rng = uu____72448;_})
            ->
            let uu____72459 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____72459
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____72471 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____72471
            then FullMatch
            else
              (let uu____72476 =
                 let uu____72485 =
                   let uu____72488 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____72488  in
                 let uu____72489 =
                   let uu____72492 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____72492  in
                 (uu____72485, uu____72489)  in
               MisMatch uu____72476)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____72498),FStar_Syntax_Syntax.Tm_uinst (g,uu____72500)) ->
            let uu____72509 = head_matches env f g  in
            FStar_All.pipe_right uu____72509 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____72510) -> HeadMatch true
        | (uu____72512,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____72516 = FStar_Const.eq_const c d  in
            if uu____72516
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____72526),FStar_Syntax_Syntax.Tm_uvar (uv',uu____72528)) ->
            let uu____72561 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____72561
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____72571),FStar_Syntax_Syntax.Tm_refine (y,uu____72573)) ->
            let uu____72582 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72582 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____72584),uu____72585) ->
            let uu____72590 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____72590 head_match
        | (uu____72591,FStar_Syntax_Syntax.Tm_refine (x,uu____72593)) ->
            let uu____72598 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72598 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____72599,FStar_Syntax_Syntax.Tm_type uu____72600) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____72602,FStar_Syntax_Syntax.Tm_arrow uu____72603) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____72634),FStar_Syntax_Syntax.Tm_app
           (head',uu____72636)) ->
            let uu____72685 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____72685 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____72687),uu____72688) ->
            let uu____72713 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____72713 head_match
        | (uu____72714,FStar_Syntax_Syntax.Tm_app (head1,uu____72716)) ->
            let uu____72741 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____72741 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____72742,FStar_Syntax_Syntax.Tm_let
           uu____72743) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____72771,FStar_Syntax_Syntax.Tm_match uu____72772) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____72818,FStar_Syntax_Syntax.Tm_abs
           uu____72819) -> HeadMatch true
        | uu____72857 ->
            let uu____72862 =
              let uu____72871 = delta_depth_of_term env t11  in
              let uu____72874 = delta_depth_of_term env t21  in
              (uu____72871, uu____72874)  in
            MisMatch uu____72862
  
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
            (let uu____72940 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____72940
             then
               let uu____72945 = FStar_Syntax_Print.term_to_string t  in
               let uu____72947 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____72945 uu____72947
             else ());
            (let uu____72952 =
               let uu____72953 = FStar_Syntax_Util.un_uinst head1  in
               uu____72953.FStar_Syntax_Syntax.n  in
             match uu____72952 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72959 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____72959 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____72973 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____72973
                        then
                          let uu____72978 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____72978
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____72983 ->
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
                      let uu____73000 =
                        let uu____73002 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____73002 = FStar_Syntax_Util.Equal  in
                      if uu____73000
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____73009 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____73009
                          then
                            let uu____73014 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____73016 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____73014 uu____73016
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____73021 -> FStar_Pervasives_Native.None)
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
            (let uu____73173 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____73173
             then
               let uu____73178 = FStar_Syntax_Print.term_to_string t11  in
               let uu____73180 = FStar_Syntax_Print.term_to_string t21  in
               let uu____73182 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____73178
                 uu____73180 uu____73182
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____73210 =
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
               match uu____73210 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____73258 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____73258 with
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
                  uu____73296),uu____73297)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73318 =
                      let uu____73327 = maybe_inline t11  in
                      let uu____73330 = maybe_inline t21  in
                      (uu____73327, uu____73330)  in
                    match uu____73318 with
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
                 (uu____73373,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____73374))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73395 =
                      let uu____73404 = maybe_inline t11  in
                      let uu____73407 = maybe_inline t21  in
                      (uu____73404, uu____73407)  in
                    match uu____73395 with
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
             | MisMatch uu____73462 -> fail1 n_delta r t11 t21
             | uu____73471 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____73486 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____73486
           then
             let uu____73491 = FStar_Syntax_Print.term_to_string t1  in
             let uu____73493 = FStar_Syntax_Print.term_to_string t2  in
             let uu____73495 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____73503 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____73520 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____73520
                    (fun uu____73555  ->
                       match uu____73555 with
                       | (t11,t21) ->
                           let uu____73563 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____73565 =
                             let uu____73567 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____73567  in
                           Prims.op_Hat uu____73563 uu____73565))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____73491 uu____73493 uu____73495 uu____73503
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____73584 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____73584 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_73599  ->
    match uu___609_73599 with
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
      let uu___1789_73648 = p  in
      let uu____73651 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____73652 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_73648.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____73651;
        FStar_TypeChecker_Common.relation =
          (uu___1789_73648.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____73652;
        FStar_TypeChecker_Common.element =
          (uu___1789_73648.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_73648.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_73648.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_73648.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_73648.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_73648.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____73667 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____73667
            (fun _73672  -> FStar_TypeChecker_Common.TProb _73672)
      | FStar_TypeChecker_Common.CProb uu____73673 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____73696 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____73696 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____73704 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____73704 with
           | (lh,lhs_args) ->
               let uu____73751 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____73751 with
                | (rh,rhs_args) ->
                    let uu____73798 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73811,FStar_Syntax_Syntax.Tm_uvar uu____73812)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____73901 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____73928,uu____73929)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____73944,FStar_Syntax_Syntax.Tm_uvar uu____73945)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73960,FStar_Syntax_Syntax.Tm_arrow
                         uu____73961) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_73991 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_73991.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_73991.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_73991.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_73991.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_73991.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_73991.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_73991.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_73991.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_73991.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73994,FStar_Syntax_Syntax.Tm_type uu____73995)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74011 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74011.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74011.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74011.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74011.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74011.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74011.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74011.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74011.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74011.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____74014,FStar_Syntax_Syntax.Tm_uvar uu____74015)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74031 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74031.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74031.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74031.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74031.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74031.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74031.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74031.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74031.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74031.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____74034,FStar_Syntax_Syntax.Tm_uvar uu____74035)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____74050,uu____74051)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____74066,FStar_Syntax_Syntax.Tm_uvar uu____74067)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____74082,uu____74083) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____73798 with
                     | (rank,tp1) ->
                         let uu____74096 =
                           FStar_All.pipe_right
                             (let uu___1860_74100 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_74100.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_74100.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_74100.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_74100.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_74100.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_74100.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_74100.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_74100.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_74100.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _74103  ->
                                FStar_TypeChecker_Common.TProb _74103)
                            in
                         (rank, uu____74096))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____74107 =
            FStar_All.pipe_right
              (let uu___1864_74111 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_74111.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_74111.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_74111.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_74111.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_74111.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_74111.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_74111.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_74111.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_74111.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _74114  -> FStar_TypeChecker_Common.CProb _74114)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____74107)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____74174 probs =
      match uu____74174 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____74255 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____74276 = rank wl.tcenv hd1  in
               (match uu____74276 with
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
                      (let uu____74337 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____74342 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____74342)
                          in
                       if uu____74337
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
          let uu____74415 = FStar_Syntax_Util.head_and_args t  in
          match uu____74415 with
          | (hd1,uu____74434) ->
              let uu____74459 =
                let uu____74460 = FStar_Syntax_Subst.compress hd1  in
                uu____74460.FStar_Syntax_Syntax.n  in
              (match uu____74459 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____74465) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____74500  ->
                           match uu____74500 with
                           | (y,uu____74509) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____74532  ->
                                       match uu____74532 with
                                       | (x,uu____74541) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____74546 -> false)
           in
        let uu____74548 = rank tcenv p  in
        match uu____74548 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____74557 -> true
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
    match projectee with | UDeferred _0 -> true | uu____74594 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____74614 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____74635 -> false
  
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
                        let uu____74698 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____74698 with
                        | (k,uu____74706) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____74719 -> false)))
            | uu____74721 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____74773 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____74781 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____74781 = (Prims.parse_int "0")))
                           in
                        if uu____74773 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____74802 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____74810 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____74810 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____74802)
               in
            let uu____74814 = filter1 u12  in
            let uu____74817 = filter1 u22  in (uu____74814, uu____74817)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____74852 = filter_out_common_univs us1 us2  in
                   (match uu____74852 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____74912 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____74912 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____74915 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____74926 =
                             let uu____74928 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____74930 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____74928 uu____74930
                              in
                           UFailed uu____74926))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74956 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74956 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74982 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74982 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____74985 ->
                   let uu____74990 =
                     let uu____74992 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____74994 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____74992 uu____74994 msg
                      in
                   UFailed uu____74990)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____74997,uu____74998) ->
              let uu____75000 =
                let uu____75002 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75004 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75002 uu____75004
                 in
              failwith uu____75000
          | (FStar_Syntax_Syntax.U_unknown ,uu____75007) ->
              let uu____75008 =
                let uu____75010 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75012 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75010 uu____75012
                 in
              failwith uu____75008
          | (uu____75015,FStar_Syntax_Syntax.U_bvar uu____75016) ->
              let uu____75018 =
                let uu____75020 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75022 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75020 uu____75022
                 in
              failwith uu____75018
          | (uu____75025,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____75026 =
                let uu____75028 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75030 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75028 uu____75030
                 in
              failwith uu____75026
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____75060 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____75060
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____75077 = occurs_univ v1 u3  in
              if uu____75077
              then
                let uu____75080 =
                  let uu____75082 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75084 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75082 uu____75084
                   in
                try_umax_components u11 u21 uu____75080
              else
                (let uu____75089 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75089)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____75101 = occurs_univ v1 u3  in
              if uu____75101
              then
                let uu____75104 =
                  let uu____75106 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75108 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75106 uu____75108
                   in
                try_umax_components u11 u21 uu____75104
              else
                (let uu____75113 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75113)
          | (FStar_Syntax_Syntax.U_max uu____75114,uu____75115) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75123 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75123
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____75129,FStar_Syntax_Syntax.U_max uu____75130) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75138 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75138
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____75144,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____75146,FStar_Syntax_Syntax.U_name uu____75147) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____75149) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____75151) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75153,FStar_Syntax_Syntax.U_succ uu____75154) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75156,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____75263 = bc1  in
      match uu____75263 with
      | (bs1,mk_cod1) ->
          let uu____75307 = bc2  in
          (match uu____75307 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____75418 = aux xs ys  in
                     (match uu____75418 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____75501 =
                       let uu____75508 = mk_cod1 xs  in ([], uu____75508)  in
                     let uu____75511 =
                       let uu____75518 = mk_cod2 ys  in ([], uu____75518)  in
                     (uu____75501, uu____75511)
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
                  let uu____75587 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____75587 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____75590 =
                    let uu____75591 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____75591 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____75590
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____75596 = has_type_guard t1 t2  in (uu____75596, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____75597 = has_type_guard t2 t1  in (uu____75597, wl)
  
let is_flex_pat :
  'Auu____75607 'Auu____75608 'Auu____75609 .
    ('Auu____75607 * 'Auu____75608 * 'Auu____75609 Prims.list) -> Prims.bool
  =
  fun uu___610_75623  ->
    match uu___610_75623 with
    | (uu____75632,uu____75633,[]) -> true
    | uu____75637 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____75670 = f  in
      match uu____75670 with
      | (uu____75677,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____75678;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____75679;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____75682;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____75683;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____75684;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____75685;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____75755  ->
                 match uu____75755 with
                 | (y,uu____75764) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____75918 =
                  let uu____75933 =
                    let uu____75936 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____75936  in
                  ((FStar_List.rev pat_binders), uu____75933)  in
                FStar_Pervasives_Native.Some uu____75918
            | (uu____75969,[]) ->
                let uu____76000 =
                  let uu____76015 =
                    let uu____76018 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____76018  in
                  ((FStar_List.rev pat_binders), uu____76015)  in
                FStar_Pervasives_Native.Some uu____76000
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____76109 =
                  let uu____76110 = FStar_Syntax_Subst.compress a  in
                  uu____76110.FStar_Syntax_Syntax.n  in
                (match uu____76109 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____76130 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____76130
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_76160 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_76160.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_76160.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____76164 =
                            let uu____76165 =
                              let uu____76172 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____76172)  in
                            FStar_Syntax_Syntax.NT uu____76165  in
                          [uu____76164]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_76188 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_76188.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_76188.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____76189 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____76229 =
                  let uu____76244 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____76244  in
                (match uu____76229 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____76319 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____76352 ->
               let uu____76353 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____76353 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____76675 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____76675
       then
         let uu____76680 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____76680
       else ());
      (let uu____76685 = next_prob probs  in
       match uu____76685 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_76712 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_76712.wl_deferred);
               ctr = (uu___2219_76712.ctr);
               defer_ok = (uu___2219_76712.defer_ok);
               smt_ok = (uu___2219_76712.smt_ok);
               umax_heuristic_ok = (uu___2219_76712.umax_heuristic_ok);
               tcenv = (uu___2219_76712.tcenv);
               wl_implicits = (uu___2219_76712.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____76721 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____76721
                 then
                   let uu____76724 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____76724
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
                           (let uu___2231_76736 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_76736.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_76736.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_76736.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_76736.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_76736.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_76736.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_76736.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_76736.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_76736.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____76762 ->
                let uu____76773 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____76844  ->
                          match uu____76844 with
                          | (c,uu____76855,uu____76856) -> c < probs.ctr))
                   in
                (match uu____76773 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____76911 =
                            let uu____76916 =
                              FStar_List.map
                                (fun uu____76934  ->
                                   match uu____76934 with
                                   | (uu____76948,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____76916, (probs.wl_implicits))  in
                          Success uu____76911
                      | uu____76956 ->
                          let uu____76967 =
                            let uu___2249_76968 = probs  in
                            let uu____76969 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____76992  ->
                                      match uu____76992 with
                                      | (uu____77001,uu____77002,y) -> y))
                               in
                            {
                              attempting = uu____76969;
                              wl_deferred = rest;
                              ctr = (uu___2249_76968.ctr);
                              defer_ok = (uu___2249_76968.defer_ok);
                              smt_ok = (uu___2249_76968.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_76968.umax_heuristic_ok);
                              tcenv = (uu___2249_76968.tcenv);
                              wl_implicits = (uu___2249_76968.wl_implicits)
                            }  in
                          solve env uu____76967))))

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
            let uu____77013 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____77013 with
            | USolved wl1 ->
                let uu____77015 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____77015
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
                  let uu____77069 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____77069 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____77072 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____77085;
                  FStar_Syntax_Syntax.vars = uu____77086;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____77089;
                  FStar_Syntax_Syntax.vars = uu____77090;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____77103,uu____77104) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____77112,FStar_Syntax_Syntax.Tm_uinst uu____77113) ->
                failwith "Impossible: expect head symbols to match"
            | uu____77121 -> USolved wl

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
            ((let uu____77133 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____77133
              then
                let uu____77138 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____77138 msg
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
               let uu____77230 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____77230 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____77285 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____77285
                then
                  let uu____77290 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____77292 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____77290 uu____77292
                else ());
               (let uu____77297 = head_matches_delta env1 wl2 t1 t2  in
                match uu____77297 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____77343 = eq_prob t1 t2 wl2  in
                         (match uu____77343 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____77364 ->
                         let uu____77373 = eq_prob t1 t2 wl2  in
                         (match uu____77373 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____77423 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____77438 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____77439 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____77438, uu____77439)
                           | FStar_Pervasives_Native.None  ->
                               let uu____77444 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____77445 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____77444, uu____77445)
                            in
                         (match uu____77423 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____77476 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____77476 with
                                | (t1_hd,t1_args) ->
                                    let uu____77521 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____77521 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____77587 =
                                              let uu____77594 =
                                                let uu____77605 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____77605 :: t1_args  in
                                              let uu____77622 =
                                                let uu____77631 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____77631 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____77680  ->
                                                   fun uu____77681  ->
                                                     fun uu____77682  ->
                                                       match (uu____77680,
                                                               uu____77681,
                                                               uu____77682)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____77732),
                                                          (a2,uu____77734))
                                                           ->
                                                           let uu____77771 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____77771
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____77594
                                                uu____77622
                                               in
                                            match uu____77587 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_77797 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_77797.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_77797.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_77797.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____77809 =
                                                  solve env1 wl'  in
                                                (match uu____77809 with
                                                 | Success (uu____77812,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_77816
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_77816.attempting);
                                                            wl_deferred =
                                                              (uu___2412_77816.wl_deferred);
                                                            ctr =
                                                              (uu___2412_77816.ctr);
                                                            defer_ok =
                                                              (uu___2412_77816.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_77816.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_77816.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_77816.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____77817 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____77850 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____77850 with
                                | (t1_base,p1_opt) ->
                                    let uu____77886 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____77886 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____77985 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____77985
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
                                               let uu____78038 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____78038
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
                                               let uu____78070 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78070
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
                                               let uu____78102 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78102
                                           | uu____78105 -> t_base  in
                                         let uu____78122 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____78122 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____78136 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____78136, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____78143 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____78143 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____78179 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____78179 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____78215 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____78215
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
                              let uu____78239 = combine t11 t21 wl2  in
                              (match uu____78239 with
                               | (t12,ps,wl3) ->
                                   ((let uu____78272 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____78272
                                     then
                                       let uu____78277 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____78277
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____78319 ts1 =
               match uu____78319 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____78382 = pairwise out t wl2  in
                        (match uu____78382 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____78418 =
               let uu____78429 = FStar_List.hd ts  in (uu____78429, [], wl1)
                in
             let uu____78438 = FStar_List.tl ts  in
             aux uu____78418 uu____78438  in
           let uu____78445 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____78445 with
           | (this_flex,this_rigid) ->
               let uu____78471 =
                 let uu____78472 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____78472.FStar_Syntax_Syntax.n  in
               (match uu____78471 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____78497 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____78497
                    then
                      let uu____78500 = destruct_flex_t this_flex wl  in
                      (match uu____78500 with
                       | (flex,wl1) ->
                           let uu____78507 = quasi_pattern env flex  in
                           (match uu____78507 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____78526 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____78526
                                  then
                                    let uu____78531 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____78531
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____78538 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_78541 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_78541.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_78541.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_78541.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_78541.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_78541.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_78541.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_78541.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_78541.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_78541.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____78538)
                | uu____78542 ->
                    ((let uu____78544 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____78544
                      then
                        let uu____78549 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____78549
                      else ());
                     (let uu____78554 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____78554 with
                      | (u,_args) ->
                          let uu____78597 =
                            let uu____78598 = FStar_Syntax_Subst.compress u
                               in
                            uu____78598.FStar_Syntax_Syntax.n  in
                          (match uu____78597 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____78626 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____78626 with
                                 | (u',uu____78645) ->
                                     let uu____78670 =
                                       let uu____78671 = whnf env u'  in
                                       uu____78671.FStar_Syntax_Syntax.n  in
                                     (match uu____78670 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____78693 -> false)
                                  in
                               let uu____78695 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_78718  ->
                                         match uu___611_78718 with
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
                                              | uu____78732 -> false)
                                         | uu____78736 -> false))
                                  in
                               (match uu____78695 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____78751 = whnf env this_rigid
                                         in
                                      let uu____78752 =
                                        FStar_List.collect
                                          (fun uu___612_78758  ->
                                             match uu___612_78758 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____78764 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____78764]
                                             | uu____78768 -> [])
                                          bounds_probs
                                         in
                                      uu____78751 :: uu____78752  in
                                    let uu____78769 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____78769 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____78802 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____78817 =
                                               let uu____78818 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____78818.FStar_Syntax_Syntax.n
                                                in
                                             match uu____78817 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____78830 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____78830)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____78841 -> bound  in
                                           let uu____78842 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____78842)  in
                                         (match uu____78802 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____78877 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____78877
                                                then
                                                  let wl'1 =
                                                    let uu___2574_78883 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_78883.wl_deferred);
                                                      ctr =
                                                        (uu___2574_78883.ctr);
                                                      defer_ok =
                                                        (uu___2574_78883.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_78883.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_78883.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_78883.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_78883.wl_implicits)
                                                    }  in
                                                  let uu____78884 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____78884
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____78890 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_78892 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_78892.wl_deferred);
                                                       ctr =
                                                         (uu___2579_78892.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_78892.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_78892.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_78892.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____78890 with
                                                | Success (uu____78894,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_78897 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_78897.wl_deferred);
                                                        ctr =
                                                          (uu___2585_78897.ctr);
                                                        defer_ok =
                                                          (uu___2585_78897.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_78897.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_78897.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_78897.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_78897.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_78899 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_78899.attempting);
                                                        wl_deferred =
                                                          (uu___2588_78899.wl_deferred);
                                                        ctr =
                                                          (uu___2588_78899.ctr);
                                                        defer_ok =
                                                          (uu___2588_78899.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_78899.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_78899.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_78899.tcenv);
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
                                                    let uu____78915 =
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
                                                    ((let uu____78929 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____78929
                                                      then
                                                        let uu____78934 =
                                                          let uu____78936 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____78936
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____78934
                                                      else ());
                                                     (let uu____78949 =
                                                        let uu____78964 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____78964)
                                                         in
                                                      match uu____78949 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____78986))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____79012 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____79012
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
                                                                  let uu____79032
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79032))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____79057 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____79057
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
                                                                    let uu____79077
                                                                    =
                                                                    let uu____79082
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79082
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____79077
                                                                    [] wl2
                                                                     in
                                                                  let uu____79088
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79088))))
                                                      | uu____79089 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____79105 when flip ->
                               let uu____79106 =
                                 let uu____79108 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79110 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____79108 uu____79110
                                  in
                               failwith uu____79106
                           | uu____79113 ->
                               let uu____79114 =
                                 let uu____79116 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79118 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____79116 uu____79118
                                  in
                               failwith uu____79114)))))

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
                      (fun uu____79154  ->
                         match uu____79154 with
                         | (x,i) ->
                             let uu____79173 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____79173, i)) bs_lhs
                     in
                  let uu____79176 = lhs  in
                  match uu____79176 with
                  | (uu____79177,u_lhs,uu____79179) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____79276 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____79286 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____79286, univ)
                             in
                          match uu____79276 with
                          | (k,univ) ->
                              let uu____79293 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____79293 with
                               | (uu____79310,u,wl3) ->
                                   let uu____79313 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____79313, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____79339 =
                              let uu____79352 =
                                let uu____79363 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____79363 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____79414  ->
                                   fun uu____79415  ->
                                     match (uu____79414, uu____79415) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____79516 =
                                           let uu____79523 =
                                             let uu____79526 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____79526
                                              in
                                           copy_uvar u_lhs [] uu____79523 wl2
                                            in
                                         (match uu____79516 with
                                          | (uu____79555,t_a,wl3) ->
                                              let uu____79558 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____79558 with
                                               | (uu____79577,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____79352
                                ([], wl1)
                               in
                            (match uu____79339 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_79633 = ct  in
                                   let uu____79634 =
                                     let uu____79637 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____79637
                                      in
                                   let uu____79652 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_79633.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_79633.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____79634;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____79652;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_79633.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_79670 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_79670.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_79670.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____79673 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____79673 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____79735 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____79735 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____79746 =
                                          let uu____79751 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____79751)  in
                                        TERM uu____79746  in
                                      let uu____79752 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____79752 with
                                       | (sub_prob,wl3) ->
                                           let uu____79766 =
                                             let uu____79767 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____79767
                                              in
                                           solve env uu____79766))
                             | (x,imp)::formals2 ->
                                 let uu____79789 =
                                   let uu____79796 =
                                     let uu____79799 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____79799
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____79796 wl1
                                    in
                                 (match uu____79789 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____79820 =
                                          let uu____79823 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____79823
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____79820 u_x
                                         in
                                      let uu____79824 =
                                        let uu____79827 =
                                          let uu____79830 =
                                            let uu____79831 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____79831, imp)  in
                                          [uu____79830]  in
                                        FStar_List.append bs_terms
                                          uu____79827
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____79824 formals2 wl2)
                              in
                           let uu____79858 = occurs_check u_lhs arrow1  in
                           (match uu____79858 with
                            | (uu____79871,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____79887 =
                                    let uu____79889 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____79889
                                     in
                                  giveup_or_defer env orig wl uu____79887
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
              (let uu____79922 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____79922
               then
                 let uu____79927 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____79930 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____79927 (rel_to_string (p_rel orig)) uu____79930
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____80057 = rhs wl1 scope env1 subst1  in
                     (match uu____80057 with
                      | (rhs_prob,wl2) ->
                          ((let uu____80078 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____80078
                            then
                              let uu____80083 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____80083
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____80161 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____80161 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_80163 = hd1  in
                       let uu____80164 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_80163.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_80163.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80164
                       }  in
                     let hd21 =
                       let uu___2773_80168 = hd2  in
                       let uu____80169 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_80168.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_80168.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80169
                       }  in
                     let uu____80172 =
                       let uu____80177 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____80177
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____80172 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____80198 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____80198
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____80205 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____80205 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____80272 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____80272
                                  in
                               ((let uu____80290 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____80290
                                 then
                                   let uu____80295 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____80297 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____80295
                                     uu____80297
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____80330 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____80366 = aux wl [] env [] bs1 bs2  in
               match uu____80366 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____80421 = attempt sub_probs wl2  in
                   solve env uu____80421)

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
            let uu___2808_80442 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_80442.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_80442.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____80455 = try_solve env wl'  in
          match uu____80455 with
          | Success (uu____80456,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_80460 = wl  in
                  {
                    attempting = (uu___2817_80460.attempting);
                    wl_deferred = (uu___2817_80460.wl_deferred);
                    ctr = (uu___2817_80460.ctr);
                    defer_ok = (uu___2817_80460.defer_ok);
                    smt_ok = (uu___2817_80460.smt_ok);
                    umax_heuristic_ok = (uu___2817_80460.umax_heuristic_ok);
                    tcenv = (uu___2817_80460.tcenv);
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
        (let uu____80472 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____80472 wl)

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
              let uu____80486 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____80486 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____80520 = lhs1  in
              match uu____80520 with
              | (uu____80523,ctx_u,uu____80525) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____80533 ->
                        let uu____80534 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____80534 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____80583 = quasi_pattern env1 lhs1  in
              match uu____80583 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____80617) ->
                  let uu____80622 = lhs1  in
                  (match uu____80622 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____80637 = occurs_check ctx_u rhs1  in
                       (match uu____80637 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____80688 =
                                let uu____80696 =
                                  let uu____80698 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____80698
                                   in
                                FStar_Util.Inl uu____80696  in
                              (uu____80688, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____80726 =
                                 let uu____80728 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____80728  in
                               if uu____80726
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____80755 =
                                    let uu____80763 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____80763  in
                                  let uu____80769 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____80755, uu____80769)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____80813 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____80813 with
              | (rhs_hd,args) ->
                  let uu____80856 = FStar_Util.prefix args  in
                  (match uu____80856 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____80928 = lhs1  in
                       (match uu____80928 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____80932 =
                              let uu____80943 =
                                let uu____80950 =
                                  let uu____80953 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____80953
                                   in
                                copy_uvar u_lhs [] uu____80950 wl1  in
                              match uu____80943 with
                              | (uu____80980,t_last_arg,wl2) ->
                                  let uu____80983 =
                                    let uu____80990 =
                                      let uu____80991 =
                                        let uu____81000 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____81000]  in
                                      FStar_List.append bs_lhs uu____80991
                                       in
                                    copy_uvar u_lhs uu____80990 t_res_lhs wl2
                                     in
                                  (match uu____80983 with
                                   | (uu____81035,lhs',wl3) ->
                                       let uu____81038 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____81038 with
                                        | (uu____81055,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____80932 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____81076 =
                                     let uu____81077 =
                                       let uu____81082 =
                                         let uu____81083 =
                                           let uu____81086 =
                                             let uu____81091 =
                                               let uu____81092 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____81092]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____81091
                                              in
                                           uu____81086
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____81083
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____81082)  in
                                     TERM uu____81077  in
                                   [uu____81076]  in
                                 let uu____81119 =
                                   let uu____81126 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____81126 with
                                   | (p1,wl3) ->
                                       let uu____81146 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____81146 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____81119 with
                                  | (sub_probs,wl3) ->
                                      let uu____81178 =
                                        let uu____81179 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____81179  in
                                      solve env1 uu____81178))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____81213 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____81213 with
                | (uu____81231,args) ->
                    (match args with | [] -> false | uu____81267 -> true)
                 in
              let is_arrow rhs2 =
                let uu____81286 =
                  let uu____81287 = FStar_Syntax_Subst.compress rhs2  in
                  uu____81287.FStar_Syntax_Syntax.n  in
                match uu____81286 with
                | FStar_Syntax_Syntax.Tm_arrow uu____81291 -> true
                | uu____81307 -> false  in
              let uu____81309 = quasi_pattern env1 lhs1  in
              match uu____81309 with
              | FStar_Pervasives_Native.None  ->
                  let uu____81320 =
                    let uu____81322 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____81322
                     in
                  giveup_or_defer env1 orig1 wl1 uu____81320
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____81331 = is_app rhs1  in
                  if uu____81331
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____81336 = is_arrow rhs1  in
                     if uu____81336
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____81341 =
                          let uu____81343 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____81343
                           in
                        giveup_or_defer env1 orig1 wl1 uu____81341))
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
                let uu____81354 = lhs  in
                (match uu____81354 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____81358 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____81358 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____81376 =
                              let uu____81380 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____81380
                               in
                            FStar_All.pipe_right uu____81376
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____81401 = occurs_check ctx_uv rhs1  in
                          (match uu____81401 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____81430 =
                                   let uu____81432 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____81432
                                    in
                                 giveup_or_defer env orig wl uu____81430
                               else
                                 (let uu____81438 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____81438
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____81445 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____81445
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____81449 =
                                         let uu____81451 =
                                           names_to_string1 fvs2  in
                                         let uu____81453 =
                                           names_to_string1 fvs1  in
                                         let uu____81455 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____81451 uu____81453
                                           uu____81455
                                          in
                                       giveup_or_defer env orig wl
                                         uu____81449)
                                    else first_order orig env wl lhs rhs1))
                      | uu____81467 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____81474 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____81474 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____81500 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____81500
                             | (FStar_Util.Inl msg,uu____81502) ->
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
                  (let uu____81547 =
                     let uu____81564 = quasi_pattern env lhs  in
                     let uu____81571 = quasi_pattern env rhs  in
                     (uu____81564, uu____81571)  in
                   match uu____81547 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____81614 = lhs  in
                       (match uu____81614 with
                        | ({ FStar_Syntax_Syntax.n = uu____81615;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____81617;_},u_lhs,uu____81619)
                            ->
                            let uu____81622 = rhs  in
                            (match uu____81622 with
                             | (uu____81623,u_rhs,uu____81625) ->
                                 let uu____81626 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____81626
                                 then
                                   let uu____81633 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____81633
                                 else
                                   (let uu____81636 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____81636 with
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
                                        let uu____81668 =
                                          let uu____81675 =
                                            let uu____81678 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____81678
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____81675
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____81668 with
                                         | (uu____81690,w,wl1) ->
                                             let w_app =
                                               let uu____81696 =
                                                 let uu____81701 =
                                                   FStar_List.map
                                                     (fun uu____81712  ->
                                                        match uu____81712
                                                        with
                                                        | (z,uu____81720) ->
                                                            let uu____81725 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____81725) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____81701
                                                  in
                                               uu____81696
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____81729 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____81729
                                               then
                                                 let uu____81734 =
                                                   let uu____81738 =
                                                     flex_t_to_string lhs  in
                                                   let uu____81740 =
                                                     let uu____81744 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____81746 =
                                                       let uu____81750 =
                                                         term_to_string w  in
                                                       let uu____81752 =
                                                         let uu____81756 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____81765 =
                                                           let uu____81769 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____81778 =
                                                             let uu____81782
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____81782]
                                                              in
                                                           uu____81769 ::
                                                             uu____81778
                                                            in
                                                         uu____81756 ::
                                                           uu____81765
                                                          in
                                                       uu____81750 ::
                                                         uu____81752
                                                        in
                                                     uu____81744 ::
                                                       uu____81746
                                                      in
                                                   uu____81738 :: uu____81740
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____81734
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____81799 =
                                                     let uu____81804 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____81804)  in
                                                   TERM uu____81799  in
                                                 let uu____81805 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____81805
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____81813 =
                                                        let uu____81818 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____81818)
                                                         in
                                                      TERM uu____81813  in
                                                    [s1; s2])
                                                  in
                                               let uu____81819 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____81819))))))
                   | uu____81820 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____81891 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____81891
            then
              let uu____81896 = FStar_Syntax_Print.term_to_string t1  in
              let uu____81898 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____81900 = FStar_Syntax_Print.term_to_string t2  in
              let uu____81902 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____81896 uu____81898 uu____81900 uu____81902
            else ());
           (let uu____81913 = FStar_Syntax_Util.head_and_args t1  in
            match uu____81913 with
            | (head1,args1) ->
                let uu____81956 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____81956 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____82026 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____82026 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____82056 =
                         let uu____82058 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____82060 = args_to_string args1  in
                         let uu____82064 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____82066 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____82058 uu____82060 uu____82064 uu____82066
                          in
                       giveup env1 uu____82056 orig
                     else
                       (let uu____82073 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____82082 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____82082 = FStar_Syntax_Util.Equal)
                           in
                        if uu____82073
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_82086 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_82086.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_82086.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_82086.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_82086.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_82086.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_82086.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_82086.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_82086.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____82096 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____82096
                                    else solve env1 wl2))
                        else
                          (let uu____82101 = base_and_refinement env1 t1  in
                           match uu____82101 with
                           | (base1,refinement1) ->
                               let uu____82126 = base_and_refinement env1 t2
                                  in
                               (match uu____82126 with
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
                                           let uu____82291 =
                                             FStar_List.fold_right
                                               (fun uu____82331  ->
                                                  fun uu____82332  ->
                                                    match (uu____82331,
                                                            uu____82332)
                                                    with
                                                    | (((a1,uu____82384),
                                                        (a2,uu____82386)),
                                                       (probs,wl3)) ->
                                                        let uu____82435 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____82435
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____82291 with
                                           | (subprobs,wl3) ->
                                               ((let uu____82478 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82478
                                                 then
                                                   let uu____82483 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____82483
                                                 else ());
                                                (let uu____82489 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____82489
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
                                                    (let uu____82516 =
                                                       mk_sub_probs wl3  in
                                                     match uu____82516 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____82532 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____82532
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____82540 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____82540))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____82564 =
                                                    mk_sub_probs wl3  in
                                                  match uu____82564 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____82578 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____82578)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____82604 =
                                           match uu____82604 with
                                           | (prob,reason) ->
                                               ((let uu____82615 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82615
                                                 then
                                                   let uu____82620 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____82622 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____82620 uu____82622
                                                     reason
                                                 else ());
                                                (let uu____82627 =
                                                   let uu____82636 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____82639 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____82636, uu____82639)
                                                    in
                                                 match uu____82627 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____82652 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____82652 with
                                                      | (head1',uu____82670)
                                                          ->
                                                          let uu____82695 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____82695
                                                           with
                                                           | (head2',uu____82713)
                                                               ->
                                                               let uu____82738
                                                                 =
                                                                 let uu____82743
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____82744
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____82743,
                                                                   uu____82744)
                                                                  in
                                                               (match uu____82738
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____82746
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82746
                                                                    then
                                                                    let uu____82751
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____82753
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____82755
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____82757
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____82751
                                                                    uu____82753
                                                                    uu____82755
                                                                    uu____82757
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____82762
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_82770
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_82770.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_82770.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_82770.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_82770.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_82770.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_82770.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_82770.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_82770.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____82772
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82772
                                                                    then
                                                                    let uu____82777
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____82777
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____82782 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____82794 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____82794 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____82802 =
                                             let uu____82803 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____82803.FStar_Syntax_Syntax.n
                                              in
                                           match uu____82802 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____82808 -> false  in
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
                                          | uu____82811 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____82814 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_82850 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_82850.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_82850.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_82850.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_82850.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_82850.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_82850.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_82850.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_82850.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____82926 = destruct_flex_t scrutinee wl1  in
             match uu____82926 with
             | ((_t,uv,_args),wl2) ->
                 let uu____82937 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____82937 with
                  | (xs,pat_term,uu____82953,uu____82954) ->
                      let uu____82959 =
                        FStar_List.fold_left
                          (fun uu____82982  ->
                             fun x  ->
                               match uu____82982 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____83003 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____83003 with
                                    | (uu____83022,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____82959 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____83043 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____83043 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_83060 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_83060.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_83060.umax_heuristic_ok);
                                    tcenv = (uu___3212_83060.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____83072 = solve env1 wl'  in
                                (match uu____83072 with
                                 | Success (uu____83075,imps) ->
                                     let wl'1 =
                                       let uu___3220_83078 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_83078.wl_deferred);
                                         ctr = (uu___3220_83078.ctr);
                                         defer_ok =
                                           (uu___3220_83078.defer_ok);
                                         smt_ok = (uu___3220_83078.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_83078.umax_heuristic_ok);
                                         tcenv = (uu___3220_83078.tcenv);
                                         wl_implicits =
                                           (uu___3220_83078.wl_implicits)
                                       }  in
                                     let uu____83079 = solve env1 wl'1  in
                                     (match uu____83079 with
                                      | Success (uu____83082,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_83086 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_83086.attempting);
                                                 wl_deferred =
                                                   (uu___3228_83086.wl_deferred);
                                                 ctr = (uu___3228_83086.ctr);
                                                 defer_ok =
                                                   (uu___3228_83086.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_83086.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_83086.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_83086.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____83087 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____83094 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____83117 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____83117
                 then
                   let uu____83122 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____83124 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____83122 uu____83124
                 else ());
                (let uu____83129 =
                   let uu____83150 =
                     let uu____83159 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____83159)  in
                   let uu____83166 =
                     let uu____83175 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____83175)  in
                   (uu____83150, uu____83166)  in
                 match uu____83129 with
                 | ((uu____83205,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____83208;
                                   FStar_Syntax_Syntax.vars = uu____83209;_}),
                    (s,t)) ->
                     let uu____83280 =
                       let uu____83282 = is_flex scrutinee  in
                       Prims.op_Negation uu____83282  in
                     if uu____83280
                     then
                       ((let uu____83293 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____83293
                         then
                           let uu____83298 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____83298
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____83317 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83317
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____83332 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83332
                           then
                             let uu____83337 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____83339 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____83337 uu____83339
                           else ());
                          (let pat_discriminates uu___613_83364 =
                             match uu___613_83364 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____83380;
                                  FStar_Syntax_Syntax.p = uu____83381;_},FStar_Pervasives_Native.None
                                ,uu____83382) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____83396;
                                  FStar_Syntax_Syntax.p = uu____83397;_},FStar_Pervasives_Native.None
                                ,uu____83398) -> true
                             | uu____83425 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____83528 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____83528 with
                                       | (uu____83530,uu____83531,t') ->
                                           let uu____83549 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____83549 with
                                            | (FullMatch ,uu____83561) ->
                                                true
                                            | (HeadMatch
                                               uu____83575,uu____83576) ->
                                                true
                                            | uu____83591 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____83628 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____83628
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____83639 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____83639 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____83727,uu____83728) ->
                                       branches1
                                   | uu____83873 -> branches  in
                                 let uu____83928 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____83937 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____83937 with
                                        | (p,uu____83941,uu____83942) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _83971  -> FStar_Util.Inr _83971)
                                   uu____83928))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84001 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84001 with
                                | (p,uu____84010,e) ->
                                    ((let uu____84029 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84029
                                      then
                                        let uu____84034 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84036 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84034 uu____84036
                                      else ());
                                     (let uu____84041 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84056  -> FStar_Util.Inr _84056)
                                        uu____84041)))))
                 | ((s,t),(uu____84059,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____84062;
                                         FStar_Syntax_Syntax.vars =
                                           uu____84063;_}))
                     ->
                     let uu____84132 =
                       let uu____84134 = is_flex scrutinee  in
                       Prims.op_Negation uu____84134  in
                     if uu____84132
                     then
                       ((let uu____84145 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____84145
                         then
                           let uu____84150 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____84150
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____84169 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84169
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____84184 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84184
                           then
                             let uu____84189 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____84191 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____84189 uu____84191
                           else ());
                          (let pat_discriminates uu___613_84216 =
                             match uu___613_84216 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____84232;
                                  FStar_Syntax_Syntax.p = uu____84233;_},FStar_Pervasives_Native.None
                                ,uu____84234) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____84248;
                                  FStar_Syntax_Syntax.p = uu____84249;_},FStar_Pervasives_Native.None
                                ,uu____84250) -> true
                             | uu____84277 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____84380 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____84380 with
                                       | (uu____84382,uu____84383,t') ->
                                           let uu____84401 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____84401 with
                                            | (FullMatch ,uu____84413) ->
                                                true
                                            | (HeadMatch
                                               uu____84427,uu____84428) ->
                                                true
                                            | uu____84443 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____84480 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____84480
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____84491 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____84491 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____84579,uu____84580) ->
                                       branches1
                                   | uu____84725 -> branches  in
                                 let uu____84780 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____84789 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____84789 with
                                        | (p,uu____84793,uu____84794) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _84823  -> FStar_Util.Inr _84823)
                                   uu____84780))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84853 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84853 with
                                | (p,uu____84862,e) ->
                                    ((let uu____84881 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84881
                                      then
                                        let uu____84886 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84888 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84886 uu____84888
                                      else ());
                                     (let uu____84893 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84908  -> FStar_Util.Inr _84908)
                                        uu____84893)))))
                 | uu____84909 ->
                     ((let uu____84931 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____84931
                       then
                         let uu____84936 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____84938 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____84936 uu____84938
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____84984 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____84984
            then
              let uu____84989 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____84991 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____84993 = FStar_Syntax_Print.term_to_string t1  in
              let uu____84995 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____84989 uu____84991 uu____84993 uu____84995
            else ());
           (let uu____85000 = head_matches_delta env1 wl1 t1 t2  in
            match uu____85000 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____85031,uu____85032) ->
                     let rec may_relate head3 =
                       let uu____85060 =
                         let uu____85061 = FStar_Syntax_Subst.compress head3
                            in
                         uu____85061.FStar_Syntax_Syntax.n  in
                       match uu____85060 with
                       | FStar_Syntax_Syntax.Tm_name uu____85065 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____85067 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____85092 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____85092 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____85094 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____85097
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____85098 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____85101,uu____85102) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____85144) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____85150) ->
                           may_relate t
                       | uu____85155 -> false  in
                     let uu____85157 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____85157 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____85178 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____85178
                          then
                            let uu____85181 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____85181 with
                             | (guard,wl2) ->
                                 let uu____85188 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____85188)
                          else
                            (let uu____85191 =
                               let uu____85193 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____85195 =
                                 let uu____85197 =
                                   let uu____85201 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____85201
                                     (fun x  ->
                                        let uu____85208 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85208)
                                    in
                                 FStar_Util.dflt "" uu____85197  in
                               let uu____85213 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____85215 =
                                 let uu____85217 =
                                   let uu____85221 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____85221
                                     (fun x  ->
                                        let uu____85228 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85228)
                                    in
                                 FStar_Util.dflt "" uu____85217  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____85193 uu____85195 uu____85213
                                 uu____85215
                                in
                             giveup env1 uu____85191 orig))
                 | (HeadMatch (true ),uu____85234) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____85249 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____85249 with
                        | (guard,wl2) ->
                            let uu____85256 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____85256)
                     else
                       (let uu____85259 =
                          let uu____85261 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____85263 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____85261 uu____85263
                           in
                        giveup env1 uu____85259 orig)
                 | (uu____85266,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_85280 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_85280.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_85280.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_85280.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_85280.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_85280.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_85280.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_85280.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_85280.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____85307 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____85307
          then
            let uu____85310 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____85310
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____85316 =
                let uu____85319 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85319  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____85316 t1);
             (let uu____85338 =
                let uu____85341 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85341  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____85338 t2);
             (let uu____85360 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____85360
              then
                let uu____85364 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____85366 =
                  let uu____85368 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____85370 =
                    let uu____85372 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____85372  in
                  Prims.op_Hat uu____85368 uu____85370  in
                let uu____85375 =
                  let uu____85377 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____85379 =
                    let uu____85381 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____85381  in
                  Prims.op_Hat uu____85377 uu____85379  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____85364 uu____85366 uu____85375
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____85388,uu____85389) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____85413,FStar_Syntax_Syntax.Tm_delayed uu____85414) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____85438,uu____85439) ->
                  let uu____85466 =
                    let uu___3432_85467 = problem  in
                    let uu____85468 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_85467.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85468;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_85467.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_85467.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_85467.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_85467.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_85467.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_85467.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_85467.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_85467.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85466 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____85469,uu____85470) ->
                  let uu____85477 =
                    let uu___3438_85478 = problem  in
                    let uu____85479 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_85478.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85479;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_85478.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_85478.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_85478.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_85478.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_85478.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_85478.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_85478.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_85478.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85477 wl
              | (uu____85480,FStar_Syntax_Syntax.Tm_ascribed uu____85481) ->
                  let uu____85508 =
                    let uu___3444_85509 = problem  in
                    let uu____85510 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_85509.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_85509.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_85509.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85510;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_85509.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_85509.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_85509.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_85509.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_85509.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_85509.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85508 wl
              | (uu____85511,FStar_Syntax_Syntax.Tm_meta uu____85512) ->
                  let uu____85519 =
                    let uu___3450_85520 = problem  in
                    let uu____85521 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_85520.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_85520.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_85520.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85521;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_85520.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_85520.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_85520.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_85520.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_85520.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_85520.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85519 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____85523),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____85525)) ->
                  let uu____85534 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____85534
              | (FStar_Syntax_Syntax.Tm_bvar uu____85535,uu____85536) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____85538,FStar_Syntax_Syntax.Tm_bvar uu____85539) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_85609 =
                    match uu___614_85609 with
                    | [] -> c
                    | bs ->
                        let uu____85637 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____85637
                     in
                  let uu____85648 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____85648 with
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
                                    let uu____85797 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____85797
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
                  let mk_t t l uu___615_85886 =
                    match uu___615_85886 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____85928 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____85928 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____86073 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____86074 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____86073
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____86074 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____86076,uu____86077) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86108 -> true
                    | uu____86128 -> false  in
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
                      (let uu____86188 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86196 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86196.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86196.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86196.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86196.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86196.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86196.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86196.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86196.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86196.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86196.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86196.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86196.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86196.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86196.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86196.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86196.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86196.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86196.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86196.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86196.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86196.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86196.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86196.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86196.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86196.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86196.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86196.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86196.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86196.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86196.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86196.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86196.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86196.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86196.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86196.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86196.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86196.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86196.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86196.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86196.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86188 with
                       | (uu____86201,ty,uu____86203) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86212 =
                                 let uu____86213 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86213.FStar_Syntax_Syntax.n  in
                               match uu____86212 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86216 ->
                                   let uu____86223 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86223
                               | uu____86224 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86227 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86227
                             then
                               let uu____86232 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86234 =
                                 let uu____86236 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86236
                                  in
                               let uu____86237 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86232 uu____86234 uu____86237
                             else ());
                            r1))
                     in
                  let uu____86242 =
                    let uu____86259 = maybe_eta t1  in
                    let uu____86266 = maybe_eta t2  in
                    (uu____86259, uu____86266)  in
                  (match uu____86242 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86308 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86308.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86308.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86308.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86308.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86308.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86308.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86308.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86308.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86329 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86329
                       then
                         let uu____86332 = destruct_flex_t not_abs wl  in
                         (match uu____86332 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86349 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86349.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86349.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86349.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86349.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86349.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86349.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86349.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86349.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86373 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86373
                       then
                         let uu____86376 = destruct_flex_t not_abs wl  in
                         (match uu____86376 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86393 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86393.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86393.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86393.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86393.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86393.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86393.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86393.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86393.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86397 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____86415,FStar_Syntax_Syntax.Tm_abs uu____86416) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86447 -> true
                    | uu____86467 -> false  in
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
                      (let uu____86527 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86535 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86535.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86535.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86535.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86535.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86535.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86535.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86535.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86535.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86535.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86535.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86535.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86535.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86535.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86535.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86535.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86535.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86535.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86535.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86535.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86535.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86535.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86535.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86535.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86535.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86535.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86535.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86535.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86535.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86535.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86535.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86535.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86535.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86535.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86535.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86535.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86535.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86535.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86535.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86535.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86535.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86527 with
                       | (uu____86540,ty,uu____86542) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86551 =
                                 let uu____86552 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86552.FStar_Syntax_Syntax.n  in
                               match uu____86551 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86555 ->
                                   let uu____86562 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86562
                               | uu____86563 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86566 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86566
                             then
                               let uu____86571 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86573 =
                                 let uu____86575 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86575
                                  in
                               let uu____86576 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86571 uu____86573 uu____86576
                             else ());
                            r1))
                     in
                  let uu____86581 =
                    let uu____86598 = maybe_eta t1  in
                    let uu____86605 = maybe_eta t2  in
                    (uu____86598, uu____86605)  in
                  (match uu____86581 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86647 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86647.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86647.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86647.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86647.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86647.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86647.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86647.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86647.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86668 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86668
                       then
                         let uu____86671 = destruct_flex_t not_abs wl  in
                         (match uu____86671 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86688 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86688.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86688.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86688.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86688.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86688.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86688.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86688.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86688.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86712 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86712
                       then
                         let uu____86715 = destruct_flex_t not_abs wl  in
                         (match uu____86715 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86732 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86732.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86732.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86732.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86732.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86732.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86732.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86732.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86732.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86736 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____86766 =
                    let uu____86771 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____86771 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_86799 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86799.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86799.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86801 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86801.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86801.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____86802,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_86817 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86817.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86817.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86819 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86819.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86819.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____86820 -> (x1, x2)  in
                  (match uu____86766 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____86839 = as_refinement false env t11  in
                       (match uu____86839 with
                        | (x12,phi11) ->
                            let uu____86847 = as_refinement false env t21  in
                            (match uu____86847 with
                             | (x22,phi21) ->
                                 ((let uu____86856 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____86856
                                   then
                                     ((let uu____86861 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____86863 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86865 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____86861
                                         uu____86863 uu____86865);
                                      (let uu____86868 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____86870 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86872 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____86868
                                         uu____86870 uu____86872))
                                   else ());
                                  (let uu____86877 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____86877 with
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
                                         let uu____86948 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____86948
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____86960 =
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
                                         (let uu____86973 =
                                            let uu____86976 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____86976
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____86973
                                            (p_guard base_prob));
                                         (let uu____86995 =
                                            let uu____86998 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____86998
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____86995
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____87017 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____87017)
                                          in
                                       let has_uvars =
                                         (let uu____87022 =
                                            let uu____87024 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____87024
                                             in
                                          Prims.op_Negation uu____87022) ||
                                           (let uu____87028 =
                                              let uu____87030 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____87030
                                               in
                                            Prims.op_Negation uu____87028)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____87034 =
                                           let uu____87039 =
                                             let uu____87048 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____87048]  in
                                           mk_t_problem wl1 uu____87039 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____87034 with
                                          | (ref_prob,wl2) ->
                                              let uu____87070 =
                                                solve env1
                                                  (let uu___3657_87072 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_87072.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_87072.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_87072.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_87072.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_87072.wl_implicits)
                                                   })
                                                 in
                                              (match uu____87070 with
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
                                               | Success uu____87089 ->
                                                   let guard =
                                                     let uu____87097 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____87097
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_87106 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_87106.attempting);
                                                       wl_deferred =
                                                         (uu___3668_87106.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_87106.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_87106.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_87106.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_87106.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_87106.wl_implicits)
                                                     }  in
                                                   let uu____87108 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____87108))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87111,FStar_Syntax_Syntax.Tm_uvar uu____87112) ->
                  let uu____87137 = destruct_flex_t t1 wl  in
                  (match uu____87137 with
                   | (f1,wl1) ->
                       let uu____87144 = destruct_flex_t t2 wl1  in
                       (match uu____87144 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87151;
                    FStar_Syntax_Syntax.pos = uu____87152;
                    FStar_Syntax_Syntax.vars = uu____87153;_},uu____87154),FStar_Syntax_Syntax.Tm_uvar
                 uu____87155) ->
                  let uu____87204 = destruct_flex_t t1 wl  in
                  (match uu____87204 with
                   | (f1,wl1) ->
                       let uu____87211 = destruct_flex_t t2 wl1  in
                       (match uu____87211 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87218,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87219;
                    FStar_Syntax_Syntax.pos = uu____87220;
                    FStar_Syntax_Syntax.vars = uu____87221;_},uu____87222))
                  ->
                  let uu____87271 = destruct_flex_t t1 wl  in
                  (match uu____87271 with
                   | (f1,wl1) ->
                       let uu____87278 = destruct_flex_t t2 wl1  in
                       (match uu____87278 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87285;
                    FStar_Syntax_Syntax.pos = uu____87286;
                    FStar_Syntax_Syntax.vars = uu____87287;_},uu____87288),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87289;
                    FStar_Syntax_Syntax.pos = uu____87290;
                    FStar_Syntax_Syntax.vars = uu____87291;_},uu____87292))
                  ->
                  let uu____87365 = destruct_flex_t t1 wl  in
                  (match uu____87365 with
                   | (f1,wl1) ->
                       let uu____87372 = destruct_flex_t t2 wl1  in
                       (match uu____87372 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____87379,uu____87380) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87393 = destruct_flex_t t1 wl  in
                  (match uu____87393 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87400;
                    FStar_Syntax_Syntax.pos = uu____87401;
                    FStar_Syntax_Syntax.vars = uu____87402;_},uu____87403),uu____87404)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87441 = destruct_flex_t t1 wl  in
                  (match uu____87441 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____87448,FStar_Syntax_Syntax.Tm_uvar uu____87449) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____87462,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87463;
                    FStar_Syntax_Syntax.pos = uu____87464;
                    FStar_Syntax_Syntax.vars = uu____87465;_},uu____87466))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87503,FStar_Syntax_Syntax.Tm_arrow uu____87504) ->
                  solve_t' env
                    (let uu___3768_87532 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87532.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87532.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87532.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87532.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87532.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87532.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87532.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87532.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87532.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87533;
                    FStar_Syntax_Syntax.pos = uu____87534;
                    FStar_Syntax_Syntax.vars = uu____87535;_},uu____87536),FStar_Syntax_Syntax.Tm_arrow
                 uu____87537) ->
                  solve_t' env
                    (let uu___3768_87589 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87589.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87589.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87589.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87589.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87589.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87589.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87589.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87589.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87589.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87590,FStar_Syntax_Syntax.Tm_uvar uu____87591) ->
                  let uu____87604 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87604
              | (uu____87605,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87606;
                    FStar_Syntax_Syntax.pos = uu____87607;
                    FStar_Syntax_Syntax.vars = uu____87608;_},uu____87609))
                  ->
                  let uu____87646 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87646
              | (FStar_Syntax_Syntax.Tm_uvar uu____87647,uu____87648) ->
                  let uu____87661 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87661
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87662;
                    FStar_Syntax_Syntax.pos = uu____87663;
                    FStar_Syntax_Syntax.vars = uu____87664;_},uu____87665),uu____87666)
                  ->
                  let uu____87703 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87703
              | (FStar_Syntax_Syntax.Tm_refine uu____87704,uu____87705) ->
                  let t21 =
                    let uu____87713 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____87713  in
                  solve_t env
                    (let uu___3803_87739 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_87739.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_87739.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_87739.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_87739.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_87739.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_87739.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_87739.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_87739.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_87739.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87740,FStar_Syntax_Syntax.Tm_refine uu____87741) ->
                  let t11 =
                    let uu____87749 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____87749  in
                  solve_t env
                    (let uu___3810_87775 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_87775.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_87775.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_87775.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_87775.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_87775.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_87775.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_87775.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_87775.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_87775.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____87857 =
                    let uu____87858 = guard_of_prob env wl problem t1 t2  in
                    match uu____87858 with
                    | (guard,wl1) ->
                        let uu____87865 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____87865
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____88084 = br1  in
                        (match uu____88084 with
                         | (p1,w1,uu____88113) ->
                             let uu____88130 = br2  in
                             (match uu____88130 with
                              | (p2,w2,uu____88153) ->
                                  let uu____88158 =
                                    let uu____88160 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____88160  in
                                  if uu____88158
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____88187 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____88187 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____88224 = br2  in
                                         (match uu____88224 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____88257 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____88257
                                                 in
                                              let uu____88262 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____88293,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____88314) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____88373 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____88373 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____88262
                                                (fun uu____88445  ->
                                                   match uu____88445 with
                                                   | (wprobs,wl2) ->
                                                       let uu____88482 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____88482
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____88503
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____88503
                                                              then
                                                                let uu____88508
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____88510
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____88508
                                                                  uu____88510
                                                              else ());
                                                             (let uu____88516
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____88516
                                                                (fun
                                                                   uu____88552
                                                                    ->
                                                                   match uu____88552
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
                    | uu____88681 -> FStar_Pervasives_Native.None  in
                  let uu____88722 = solve_branches wl brs1 brs2  in
                  (match uu____88722 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____88773 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____88773 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____88807 =
                                FStar_List.map
                                  (fun uu____88819  ->
                                     match uu____88819 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____88807  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____88828 =
                              let uu____88829 =
                                let uu____88830 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____88830
                                  (let uu___3909_88838 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_88838.attempting);
                                     wl_deferred =
                                       (uu___3909_88838.wl_deferred);
                                     ctr = (uu___3909_88838.ctr);
                                     defer_ok = (uu___3909_88838.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_88838.umax_heuristic_ok);
                                     tcenv = (uu___3909_88838.tcenv);
                                     wl_implicits =
                                       (uu___3909_88838.wl_implicits)
                                   })
                                 in
                              solve env uu____88829  in
                            (match uu____88828 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____88843 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____88850,uu____88851) ->
                  let head1 =
                    let uu____88875 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____88875
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____88921 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____88921
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____88967 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____88967
                    then
                      let uu____88971 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____88973 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____88975 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____88971 uu____88973 uu____88975
                    else ());
                   (let no_free_uvars t =
                      (let uu____88989 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____88989) &&
                        (let uu____88993 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____88993)
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
                      let uu____89010 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89010 = FStar_Syntax_Util.Equal  in
                    let uu____89011 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89011
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89015 = equal t1 t2  in
                         (if uu____89015
                          then
                            let uu____89018 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89018
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89023 =
                            let uu____89030 = equal t1 t2  in
                            if uu____89030
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89043 = mk_eq2 wl env orig t1 t2  in
                               match uu____89043 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89023 with
                          | (guard,wl1) ->
                              let uu____89064 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89064))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____89067,uu____89068) ->
                  let head1 =
                    let uu____89076 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89076
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89122 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89122
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89168 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89168
                    then
                      let uu____89172 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89174 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89176 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89172 uu____89174 uu____89176
                    else ());
                   (let no_free_uvars t =
                      (let uu____89190 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89190) &&
                        (let uu____89194 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89194)
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
                      let uu____89211 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89211 = FStar_Syntax_Util.Equal  in
                    let uu____89212 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89212
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89216 = equal t1 t2  in
                         (if uu____89216
                          then
                            let uu____89219 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89219
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89224 =
                            let uu____89231 = equal t1 t2  in
                            if uu____89231
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89244 = mk_eq2 wl env orig t1 t2  in
                               match uu____89244 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89224 with
                          | (guard,wl1) ->
                              let uu____89265 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89265))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____89268,uu____89269) ->
                  let head1 =
                    let uu____89271 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89271
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89317 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89317
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89363 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89363
                    then
                      let uu____89367 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89369 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89371 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89367 uu____89369 uu____89371
                    else ());
                   (let no_free_uvars t =
                      (let uu____89385 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89385) &&
                        (let uu____89389 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89389)
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
                      let uu____89406 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89406 = FStar_Syntax_Util.Equal  in
                    let uu____89407 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89407
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89411 = equal t1 t2  in
                         (if uu____89411
                          then
                            let uu____89414 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89414
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89419 =
                            let uu____89426 = equal t1 t2  in
                            if uu____89426
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89439 = mk_eq2 wl env orig t1 t2  in
                               match uu____89439 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89419 with
                          | (guard,wl1) ->
                              let uu____89460 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89460))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____89463,uu____89464) ->
                  let head1 =
                    let uu____89466 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89466
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89512 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89512
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89558 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89558
                    then
                      let uu____89562 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89564 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89566 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89562 uu____89564 uu____89566
                    else ());
                   (let no_free_uvars t =
                      (let uu____89580 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89580) &&
                        (let uu____89584 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89584)
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
                      let uu____89601 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89601 = FStar_Syntax_Util.Equal  in
                    let uu____89602 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89602
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89606 = equal t1 t2  in
                         (if uu____89606
                          then
                            let uu____89609 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89609
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89614 =
                            let uu____89621 = equal t1 t2  in
                            if uu____89621
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89634 = mk_eq2 wl env orig t1 t2  in
                               match uu____89634 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89614 with
                          | (guard,wl1) ->
                              let uu____89655 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89655))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____89658,uu____89659) ->
                  let head1 =
                    let uu____89661 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89661
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89707 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89707
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89753 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89753
                    then
                      let uu____89757 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89759 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89761 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89757 uu____89759 uu____89761
                    else ());
                   (let no_free_uvars t =
                      (let uu____89775 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89775) &&
                        (let uu____89779 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89779)
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
                      let uu____89796 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89796 = FStar_Syntax_Util.Equal  in
                    let uu____89797 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89797
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89801 = equal t1 t2  in
                         (if uu____89801
                          then
                            let uu____89804 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89804
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89809 =
                            let uu____89816 = equal t1 t2  in
                            if uu____89816
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89829 = mk_eq2 wl env orig t1 t2  in
                               match uu____89829 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89809 with
                          | (guard,wl1) ->
                              let uu____89850 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89850))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____89853,uu____89854) ->
                  let head1 =
                    let uu____89872 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89872
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89918 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89918
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89964 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89964
                    then
                      let uu____89968 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89970 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89972 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89968 uu____89970 uu____89972
                    else ());
                   (let no_free_uvars t =
                      (let uu____89986 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89986) &&
                        (let uu____89990 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89990)
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
                      let uu____90007 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90007 = FStar_Syntax_Util.Equal  in
                    let uu____90008 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90008
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90012 = equal t1 t2  in
                         (if uu____90012
                          then
                            let uu____90015 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90015
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90020 =
                            let uu____90027 = equal t1 t2  in
                            if uu____90027
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90040 = mk_eq2 wl env orig t1 t2  in
                               match uu____90040 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90020 with
                          | (guard,wl1) ->
                              let uu____90061 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90061))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90064,FStar_Syntax_Syntax.Tm_match uu____90065) ->
                  let head1 =
                    let uu____90089 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90089
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90135 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90135
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90181 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90181
                    then
                      let uu____90185 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90187 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90189 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90185 uu____90187 uu____90189
                    else ());
                   (let no_free_uvars t =
                      (let uu____90203 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90203) &&
                        (let uu____90207 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90207)
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
                      let uu____90224 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90224 = FStar_Syntax_Util.Equal  in
                    let uu____90225 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90225
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90229 = equal t1 t2  in
                         (if uu____90229
                          then
                            let uu____90232 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90232
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90237 =
                            let uu____90244 = equal t1 t2  in
                            if uu____90244
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90257 = mk_eq2 wl env orig t1 t2  in
                               match uu____90257 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90237 with
                          | (guard,wl1) ->
                              let uu____90278 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90278))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90281,FStar_Syntax_Syntax.Tm_uinst uu____90282) ->
                  let head1 =
                    let uu____90290 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90290
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90330 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90330
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90370 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90370
                    then
                      let uu____90374 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90376 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90378 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90374 uu____90376 uu____90378
                    else ());
                   (let no_free_uvars t =
                      (let uu____90392 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90392) &&
                        (let uu____90396 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90396)
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
                      let uu____90413 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90413 = FStar_Syntax_Util.Equal  in
                    let uu____90414 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90414
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90418 = equal t1 t2  in
                         (if uu____90418
                          then
                            let uu____90421 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90421
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90426 =
                            let uu____90433 = equal t1 t2  in
                            if uu____90433
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90446 = mk_eq2 wl env orig t1 t2  in
                               match uu____90446 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90426 with
                          | (guard,wl1) ->
                              let uu____90467 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90467))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90470,FStar_Syntax_Syntax.Tm_name uu____90471) ->
                  let head1 =
                    let uu____90473 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90473
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90513 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90513
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90553 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90553
                    then
                      let uu____90557 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90559 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90561 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90557 uu____90559 uu____90561
                    else ());
                   (let no_free_uvars t =
                      (let uu____90575 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90575) &&
                        (let uu____90579 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90579)
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
                      let uu____90596 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90596 = FStar_Syntax_Util.Equal  in
                    let uu____90597 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90597
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90601 = equal t1 t2  in
                         (if uu____90601
                          then
                            let uu____90604 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90604
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90609 =
                            let uu____90616 = equal t1 t2  in
                            if uu____90616
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90629 = mk_eq2 wl env orig t1 t2  in
                               match uu____90629 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90609 with
                          | (guard,wl1) ->
                              let uu____90650 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90650))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90653,FStar_Syntax_Syntax.Tm_constant uu____90654) ->
                  let head1 =
                    let uu____90656 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90656
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90696 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90696
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90736 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90736
                    then
                      let uu____90740 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90742 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90744 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90740 uu____90742 uu____90744
                    else ());
                   (let no_free_uvars t =
                      (let uu____90758 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90758) &&
                        (let uu____90762 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90762)
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
                      let uu____90779 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90779 = FStar_Syntax_Util.Equal  in
                    let uu____90780 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90780
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90784 = equal t1 t2  in
                         (if uu____90784
                          then
                            let uu____90787 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90787
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90792 =
                            let uu____90799 = equal t1 t2  in
                            if uu____90799
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90812 = mk_eq2 wl env orig t1 t2  in
                               match uu____90812 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90792 with
                          | (guard,wl1) ->
                              let uu____90833 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90833))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90836,FStar_Syntax_Syntax.Tm_fvar uu____90837) ->
                  let head1 =
                    let uu____90839 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90839
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90879 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90879
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90919 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90919
                    then
                      let uu____90923 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90925 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90927 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90923 uu____90925 uu____90927
                    else ());
                   (let no_free_uvars t =
                      (let uu____90941 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90941) &&
                        (let uu____90945 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90945)
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
                      let uu____90962 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90962 = FStar_Syntax_Util.Equal  in
                    let uu____90963 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90963
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90967 = equal t1 t2  in
                         (if uu____90967
                          then
                            let uu____90970 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90970
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90975 =
                            let uu____90982 = equal t1 t2  in
                            if uu____90982
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90995 = mk_eq2 wl env orig t1 t2  in
                               match uu____90995 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90975 with
                          | (guard,wl1) ->
                              let uu____91016 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91016))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____91019,FStar_Syntax_Syntax.Tm_app uu____91020) ->
                  let head1 =
                    let uu____91038 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____91038
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____91078 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____91078
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____91118 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____91118
                    then
                      let uu____91122 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____91124 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____91126 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____91122 uu____91124 uu____91126
                    else ());
                   (let no_free_uvars t =
                      (let uu____91140 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____91140) &&
                        (let uu____91144 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____91144)
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
                      let uu____91161 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____91161 = FStar_Syntax_Util.Equal  in
                    let uu____91162 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____91162
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____91166 = equal t1 t2  in
                         (if uu____91166
                          then
                            let uu____91169 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____91169
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____91174 =
                            let uu____91181 = equal t1 t2  in
                            if uu____91181
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91194 = mk_eq2 wl env orig t1 t2  in
                               match uu____91194 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____91174 with
                          | (guard,wl1) ->
                              let uu____91215 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91215))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____91218,FStar_Syntax_Syntax.Tm_let uu____91219) ->
                  let uu____91246 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____91246
                  then
                    let uu____91249 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____91249
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____91253,uu____91254) ->
                  let uu____91268 =
                    let uu____91274 =
                      let uu____91276 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91278 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91280 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91282 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91276 uu____91278 uu____91280 uu____91282
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91274)
                     in
                  FStar_Errors.raise_error uu____91268
                    t1.FStar_Syntax_Syntax.pos
              | (uu____91286,FStar_Syntax_Syntax.Tm_let uu____91287) ->
                  let uu____91301 =
                    let uu____91307 =
                      let uu____91309 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91311 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91313 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91315 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91309 uu____91311 uu____91313 uu____91315
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91307)
                     in
                  FStar_Errors.raise_error uu____91301
                    t1.FStar_Syntax_Syntax.pos
              | uu____91319 -> giveup env "head tag mismatch" orig))))

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
          (let uu____91383 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____91383
           then
             let uu____91388 =
               let uu____91390 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____91390  in
             let uu____91391 =
               let uu____91393 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____91393  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____91388 uu____91391
           else ());
          (let uu____91397 =
             let uu____91399 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____91399  in
           if uu____91397
           then
             let uu____91402 =
               let uu____91404 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____91406 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____91404 uu____91406
                in
             giveup env uu____91402 orig
           else
             (let uu____91411 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____91411 with
              | (ret_sub_prob,wl1) ->
                  let uu____91419 =
                    FStar_List.fold_right2
                      (fun uu____91456  ->
                         fun uu____91457  ->
                           fun uu____91458  ->
                             match (uu____91456, uu____91457, uu____91458)
                             with
                             | ((a1,uu____91502),(a2,uu____91504),(arg_sub_probs,wl2))
                                 ->
                                 let uu____91537 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____91537 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____91419 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____91567 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____91567  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____91575 = attempt sub_probs wl3  in
                       solve env uu____91575)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____91598 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____91601)::[] -> wp1
              | uu____91626 ->
                  let uu____91637 =
                    let uu____91639 =
                      let uu____91641 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____91641  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____91639
                     in
                  failwith uu____91637
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____91648 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____91648]
              | x -> x  in
            let uu____91650 =
              let uu____91661 =
                let uu____91670 =
                  let uu____91671 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____91671 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____91670  in
              [uu____91661]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____91650;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____91689 = lift_c1 ()  in solve_eq uu____91689 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_91698  ->
                       match uu___616_91698 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____91703 -> false))
                in
             let uu____91705 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____91735)::uu____91736,(wp2,uu____91738)::uu____91739)
                   -> (wp1, wp2)
               | uu____91812 ->
                   let uu____91837 =
                     let uu____91843 =
                       let uu____91845 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____91847 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____91845 uu____91847
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____91843)
                      in
                   FStar_Errors.raise_error uu____91837
                     env.FStar_TypeChecker_Env.range
                in
             match uu____91705 with
             | (wpc1,wpc2) ->
                 let uu____91857 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____91857
                 then
                   let uu____91862 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____91862 wl
                 else
                   (let uu____91866 =
                      let uu____91873 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____91873  in
                    match uu____91866 with
                    | (c2_decl,qualifiers) ->
                        let uu____91894 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____91894
                        then
                          let c1_repr =
                            let uu____91901 =
                              let uu____91902 =
                                let uu____91903 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____91903  in
                              let uu____91904 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91902 uu____91904
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91901
                             in
                          let c2_repr =
                            let uu____91906 =
                              let uu____91907 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____91908 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91907 uu____91908
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91906
                             in
                          let uu____91909 =
                            let uu____91914 =
                              let uu____91916 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____91918 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____91916 uu____91918
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____91914
                             in
                          (match uu____91909 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____91924 = attempt [prob] wl2  in
                               solve env uu____91924)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____91939 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____91939
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____91948 =
                                     let uu____91955 =
                                       let uu____91956 =
                                         let uu____91973 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____91976 =
                                           let uu____91987 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____91996 =
                                             let uu____92007 =
                                               let uu____92016 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____92016
                                                in
                                             [uu____92007]  in
                                           uu____91987 :: uu____91996  in
                                         (uu____91973, uu____91976)  in
                                       FStar_Syntax_Syntax.Tm_app uu____91956
                                        in
                                     FStar_Syntax_Syntax.mk uu____91955  in
                                   uu____91948 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____92068 =
                                    let uu____92075 =
                                      let uu____92076 =
                                        let uu____92093 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____92096 =
                                          let uu____92107 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____92116 =
                                            let uu____92127 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____92136 =
                                              let uu____92147 =
                                                let uu____92156 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____92156
                                                 in
                                              [uu____92147]  in
                                            uu____92127 :: uu____92136  in
                                          uu____92107 :: uu____92116  in
                                        (uu____92093, uu____92096)  in
                                      FStar_Syntax_Syntax.Tm_app uu____92076
                                       in
                                    FStar_Syntax_Syntax.mk uu____92075  in
                                  uu____92068 FStar_Pervasives_Native.None r)
                              in
                           (let uu____92213 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92213
                            then
                              let uu____92218 =
                                let uu____92220 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____92220
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____92218
                            else ());
                           (let uu____92224 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____92224 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____92233 =
                                    let uu____92236 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _92239  ->
                                         FStar_Pervasives_Native.Some _92239)
                                      uu____92236
                                     in
                                  solve_prob orig uu____92233 [] wl1  in
                                let uu____92240 = attempt [base_prob] wl2  in
                                solve env uu____92240))))
           in
        let uu____92241 = FStar_Util.physical_equality c1 c2  in
        if uu____92241
        then
          let uu____92244 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____92244
        else
          ((let uu____92248 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____92248
            then
              let uu____92253 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____92255 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____92253
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____92255
            else ());
           (let uu____92260 =
              let uu____92269 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____92272 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____92269, uu____92272)  in
            match uu____92260 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92290),FStar_Syntax_Syntax.Total
                    (t2,uu____92292)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____92309 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92309 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92311,FStar_Syntax_Syntax.Total uu____92312) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92331),FStar_Syntax_Syntax.Total
                    (t2,uu____92333)) ->
                     let uu____92350 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92350 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92353),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92355)) ->
                     let uu____92372 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92372 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92375),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92377)) ->
                     let uu____92394 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92394 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92396,FStar_Syntax_Syntax.Comp uu____92397) ->
                     let uu____92406 =
                       let uu___4158_92409 = problem  in
                       let uu____92412 =
                         let uu____92413 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92413
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92409.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92412;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92409.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92409.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92409.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92409.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92409.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92409.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92409.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92409.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92406 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____92414,FStar_Syntax_Syntax.Comp uu____92415) ->
                     let uu____92424 =
                       let uu___4158_92427 = problem  in
                       let uu____92430 =
                         let uu____92431 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92431
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92427.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92430;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92427.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92427.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92427.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92427.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92427.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92427.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92427.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92427.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92424 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92432,FStar_Syntax_Syntax.GTotal uu____92433) ->
                     let uu____92442 =
                       let uu___4170_92445 = problem  in
                       let uu____92448 =
                         let uu____92449 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92449
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92445.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92445.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92445.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92448;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92445.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92445.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92445.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92445.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92445.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92445.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92442 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92450,FStar_Syntax_Syntax.Total uu____92451) ->
                     let uu____92460 =
                       let uu___4170_92463 = problem  in
                       let uu____92466 =
                         let uu____92467 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92467
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92463.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92463.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92463.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92466;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92463.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92463.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92463.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92463.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92463.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92463.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92460 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92468,FStar_Syntax_Syntax.Comp uu____92469) ->
                     let uu____92470 =
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
                     if uu____92470
                     then
                       let uu____92473 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____92473 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____92480 =
                            let uu____92485 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____92485
                            then (c1_comp, c2_comp)
                            else
                              (let uu____92494 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____92495 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____92494, uu____92495))
                             in
                          match uu____92480 with
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
                           (let uu____92503 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92503
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____92511 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____92511 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____92514 =
                                  let uu____92516 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____92518 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____92516 uu____92518
                                   in
                                giveup env uu____92514 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____92529 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____92529 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____92579 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____92579 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____92604 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____92635  ->
                match uu____92635 with
                | (u1,u2) ->
                    let uu____92643 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____92645 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____92643 uu____92645))
         in
      FStar_All.pipe_right uu____92604 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____92682,[])) when
          let uu____92709 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____92709 -> "{}"
      | uu____92712 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____92739 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____92739
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____92751 =
              FStar_List.map
                (fun uu____92764  ->
                   match uu____92764 with
                   | (uu____92771,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____92751 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____92782 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____92782 imps
  
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
                  let uu____92839 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____92839
                  then
                    let uu____92847 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____92849 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____92847
                      (rel_to_string rel) uu____92849
                  else "TOP"  in
                let uu____92855 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____92855 with
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
              let uu____92915 =
                let uu____92918 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _92921  -> FStar_Pervasives_Native.Some _92921)
                  uu____92918
                 in
              FStar_Syntax_Syntax.new_bv uu____92915 t1  in
            let uu____92922 =
              let uu____92927 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____92927
               in
            match uu____92922 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____92987 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____92987
         then
           let uu____92992 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____92992
         else ());
        (let uu____92999 =
           FStar_Util.record_time (fun uu____93006  -> solve env probs)  in
         match uu____92999 with
         | (sol,ms) ->
             ((let uu____93018 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____93018
               then
                 let uu____93023 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____93023
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____93036 =
                     FStar_Util.record_time
                       (fun uu____93043  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____93036 with
                    | ((),ms1) ->
                        ((let uu____93054 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____93054
                          then
                            let uu____93059 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____93059
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____93073 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____93073
                     then
                       let uu____93080 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____93080
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
          ((let uu____93107 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____93107
            then
              let uu____93112 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____93112
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____93119 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____93119
             then
               let uu____93124 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____93124
             else ());
            (let f2 =
               let uu____93130 =
                 let uu____93131 = FStar_Syntax_Util.unmeta f1  in
                 uu____93131.FStar_Syntax_Syntax.n  in
               match uu____93130 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____93135 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_93136 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_93136.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_93136.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_93136.FStar_TypeChecker_Env.implicits)
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
            let uu____93191 =
              let uu____93192 =
                let uu____93193 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _93194  ->
                       FStar_TypeChecker_Common.NonTrivial _93194)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____93193;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____93192  in
            FStar_All.pipe_left
              (fun _93201  -> FStar_Pervasives_Native.Some _93201)
              uu____93191
  
let with_guard_no_simp :
  'Auu____93211 .
    'Auu____93211 ->
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
            let uu____93234 =
              let uu____93235 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _93236  -> FStar_TypeChecker_Common.NonTrivial _93236)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____93235;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____93234
  
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
          (let uu____93269 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____93269
           then
             let uu____93274 = FStar_Syntax_Print.term_to_string t1  in
             let uu____93276 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____93274
               uu____93276
           else ());
          (let uu____93281 =
             let uu____93286 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____93286
              in
           match uu____93281 with
           | (prob,wl) ->
               let g =
                 let uu____93294 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____93304  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____93294  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____93340 = try_teq true env t1 t2  in
        match uu____93340 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____93345 = FStar_TypeChecker_Env.get_range env  in
              let uu____93346 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____93345 uu____93346);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____93354 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____93354
              then
                let uu____93359 = FStar_Syntax_Print.term_to_string t1  in
                let uu____93361 = FStar_Syntax_Print.term_to_string t2  in
                let uu____93363 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____93359
                  uu____93361 uu____93363
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
          let uu____93389 = FStar_TypeChecker_Env.get_range env  in
          let uu____93390 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____93389 uu____93390
  
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
        (let uu____93419 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____93419
         then
           let uu____93424 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____93426 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____93424 uu____93426
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____93437 =
           let uu____93444 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____93444 "sub_comp"
            in
         match uu____93437 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____93457 =
                 FStar_Util.record_time
                   (fun uu____93469  ->
                      let uu____93470 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____93481  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____93470)
                  in
               match uu____93457 with
               | (r,ms) ->
                   ((let uu____93512 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____93512
                     then
                       let uu____93517 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____93519 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____93521 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____93517 uu____93519
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____93521
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
      fun uu____93559  ->
        match uu____93559 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____93602 =
                 let uu____93608 =
                   let uu____93610 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____93612 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____93610 uu____93612
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____93608)  in
               let uu____93616 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____93602 uu____93616)
               in
            let equiv1 v1 v' =
              let uu____93629 =
                let uu____93634 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____93635 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____93634, uu____93635)  in
              match uu____93629 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____93655 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____93686 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____93686 with
                      | FStar_Syntax_Syntax.U_unif uu____93693 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____93722  ->
                                    match uu____93722 with
                                    | (u,v') ->
                                        let uu____93731 = equiv1 v1 v'  in
                                        if uu____93731
                                        then
                                          let uu____93736 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____93736 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____93757 -> []))
               in
            let uu____93762 =
              let wl =
                let uu___4377_93766 = empty_worklist env  in
                {
                  attempting = (uu___4377_93766.attempting);
                  wl_deferred = (uu___4377_93766.wl_deferred);
                  ctr = (uu___4377_93766.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_93766.smt_ok);
                  umax_heuristic_ok = (uu___4377_93766.umax_heuristic_ok);
                  tcenv = (uu___4377_93766.tcenv);
                  wl_implicits = (uu___4377_93766.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____93785  ->
                      match uu____93785 with
                      | (lb,v1) ->
                          let uu____93792 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____93792 with
                           | USolved wl1 -> ()
                           | uu____93795 -> fail1 lb v1)))
               in
            let rec check_ineq uu____93806 =
              match uu____93806 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____93818) -> true
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
                      uu____93842,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____93844,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____93855) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____93863,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____93872 -> false)
               in
            let uu____93878 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____93895  ->
                      match uu____93895 with
                      | (u,v1) ->
                          let uu____93903 = check_ineq (u, v1)  in
                          if uu____93903
                          then true
                          else
                            ((let uu____93911 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____93911
                              then
                                let uu____93916 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____93918 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____93916
                                  uu____93918
                              else ());
                             false)))
               in
            if uu____93878
            then ()
            else
              ((let uu____93928 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____93928
                then
                  ((let uu____93934 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____93934);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____93946 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____93946))
                else ());
               (let uu____93959 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____93959))
  
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
        let fail1 uu____94033 =
          match uu____94033 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_94059 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_94059.attempting);
            wl_deferred = (uu___4454_94059.wl_deferred);
            ctr = (uu___4454_94059.ctr);
            defer_ok;
            smt_ok = (uu___4454_94059.smt_ok);
            umax_heuristic_ok = (uu___4454_94059.umax_heuristic_ok);
            tcenv = (uu___4454_94059.tcenv);
            wl_implicits = (uu___4454_94059.wl_implicits)
          }  in
        (let uu____94062 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____94062
         then
           let uu____94067 = FStar_Util.string_of_bool defer_ok  in
           let uu____94069 = wl_to_string wl  in
           let uu____94071 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____94067 uu____94069 uu____94071
         else ());
        (let g1 =
           let uu____94077 = solve_and_commit env wl fail1  in
           match uu____94077 with
           | FStar_Pervasives_Native.Some
               (uu____94084::uu____94085,uu____94086) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_94115 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_94115.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_94115.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____94116 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_94125 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_94125.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_94125.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_94125.FStar_TypeChecker_Env.implicits)
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
    let uu____94179 = FStar_ST.op_Bang last_proof_ns  in
    match uu____94179 with
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
            let uu___4493_94304 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_94304.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_94304.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_94304.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____94305 =
            let uu____94307 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____94307  in
          if uu____94305
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____94319 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____94320 =
                       let uu____94322 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____94322
                        in
                     FStar_Errors.diag uu____94319 uu____94320)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____94330 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____94331 =
                        let uu____94333 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____94333
                         in
                      FStar_Errors.diag uu____94330 uu____94331)
                   else ();
                   (let uu____94339 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____94339
                      "discharge_guard'" env vc1);
                   (let uu____94341 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____94341 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____94350 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94351 =
                                let uu____94353 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____94353
                                 in
                              FStar_Errors.diag uu____94350 uu____94351)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____94363 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94364 =
                                let uu____94366 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____94366
                                 in
                              FStar_Errors.diag uu____94363 uu____94364)
                           else ();
                           (let vcs =
                              let uu____94380 = FStar_Options.use_tactics ()
                                 in
                              if uu____94380
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____94402  ->
                                     (let uu____94404 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____94404);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____94448  ->
                                              match uu____94448 with
                                              | (env1,goal,opts) ->
                                                  let uu____94464 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____94464, opts)))))
                              else
                                (let uu____94467 =
                                   let uu____94474 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____94474)  in
                                 [uu____94467])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____94507  ->
                                    match uu____94507 with
                                    | (env1,goal,opts) ->
                                        let uu____94517 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____94517 with
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
                                                (let uu____94529 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94530 =
                                                   let uu____94532 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____94534 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____94532 uu____94534
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94529 uu____94530)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____94541 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94542 =
                                                   let uu____94544 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____94544
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94541 uu____94542)
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
      let uu____94562 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____94562 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____94571 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____94571
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____94585 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____94585 with
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
        let uu____94615 = try_teq false env t1 t2  in
        match uu____94615 with
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
            let uu____94659 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____94659 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____94672 ->
                     let uu____94685 =
                       let uu____94686 = FStar_Syntax_Subst.compress r  in
                       uu____94686.FStar_Syntax_Syntax.n  in
                     (match uu____94685 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____94691) ->
                          unresolved ctx_u'
                      | uu____94708 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____94732 = acc  in
            match uu____94732 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____94751 = hd1  in
                     (match uu____94751 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____94762 = unresolved ctx_u  in
                             if uu____94762
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____94786 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____94786
                                     then
                                       let uu____94790 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____94790
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____94799 = teq_nosmt env1 t tm
                                          in
                                       match uu____94799 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_94809 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_94809.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_94809.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_94809.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_94809.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_94809.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_94809.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_94809.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_94817 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_94817.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_94817.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_94817.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_94828 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_94828.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_94828.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_94828.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_94828.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_94828.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_94828.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_94828.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_94828.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_94828.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_94828.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_94828.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_94828.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_94828.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_94828.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_94828.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_94828.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_94828.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_94828.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_94828.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_94828.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_94828.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_94828.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_94828.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_94828.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_94828.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_94828.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_94828.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_94828.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_94828.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_94828.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_94828.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_94828.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_94828.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_94828.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_94828.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_94828.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_94828.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_94828.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_94828.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_94828.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_94828.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_94828.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_94832 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_94832.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_94832.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_94832.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_94832.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_94832.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_94832.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_94832.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_94832.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_94832.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_94832.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_94832.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_94832.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_94832.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_94832.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_94832.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_94832.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_94832.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_94832.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_94832.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_94832.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_94832.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_94832.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_94832.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_94832.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_94832.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_94832.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_94832.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_94832.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_94832.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_94832.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_94832.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_94832.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_94832.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_94832.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_94832.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_94832.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_94832.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_94832.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_94832.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_94832.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_94832.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_94832.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____94837 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____94837
                                   then
                                     let uu____94842 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____94844 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____94846 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____94848 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____94842 uu____94844 uu____94846
                                       reason uu____94848
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_94855  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____94862 =
                                             let uu____94872 =
                                               let uu____94880 =
                                                 let uu____94882 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____94884 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____94886 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____94882 uu____94884
                                                   uu____94886
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____94880, r)
                                                in
                                             [uu____94872]  in
                                           FStar_Errors.add_errors
                                             uu____94862);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_94906 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_94906.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_94906.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_94906.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____94910 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____94921  ->
                                               let uu____94922 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____94924 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____94926 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____94922 uu____94924
                                                 reason uu____94926)) env2 g2
                                         true
                                        in
                                     match uu____94910 with
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
          let uu___4640_94934 = g  in
          let uu____94935 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_94934.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_94934.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_94934.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____94935
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
        let uu____94978 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____94978 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____94979 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____94979
      | imp::uu____94981 ->
          let uu____94984 =
            let uu____94990 =
              let uu____94992 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____94994 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____94992 uu____94994 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____94990)
             in
          FStar_Errors.raise_error uu____94984
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95016 = teq_nosmt env t1 t2  in
        match uu____95016 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_95035 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_95035.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_95035.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_95035.FStar_TypeChecker_Env.implicits)
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
        (let uu____95071 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95071
         then
           let uu____95076 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95078 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____95076
             uu____95078
         else ());
        (let uu____95083 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95083 with
         | (prob,x,wl) ->
             let g =
               let uu____95102 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____95113  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95102  in
             ((let uu____95134 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____95134
               then
                 let uu____95139 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____95141 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____95143 =
                   let uu____95145 = FStar_Util.must g  in
                   guard_to_string env uu____95145  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____95139 uu____95141 uu____95143
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
        let uu____95182 = check_subtyping env t1 t2  in
        match uu____95182 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95201 =
              let uu____95202 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____95202 g  in
            FStar_Pervasives_Native.Some uu____95201
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95221 = check_subtyping env t1 t2  in
        match uu____95221 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95240 =
              let uu____95241 =
                let uu____95242 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____95242]  in
              FStar_TypeChecker_Env.close_guard env uu____95241 g  in
            FStar_Pervasives_Native.Some uu____95240
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____95280 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95280
         then
           let uu____95285 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95287 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____95285
             uu____95287
         else ());
        (let uu____95292 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95292 with
         | (prob,x,wl) ->
             let g =
               let uu____95307 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____95318  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95307  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____95342 =
                      let uu____95343 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____95343]  in
                    FStar_TypeChecker_Env.close_guard env uu____95342 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95384 = subtype_nosmt env t1 t2  in
        match uu____95384 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  