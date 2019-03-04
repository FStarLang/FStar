open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____65155 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____65191 -> false
  
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
                    let uu____65615 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____65615;
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
                     (let uu___656_65647 = wl  in
                      {
                        attempting = (uu___656_65647.attempting);
                        wl_deferred = (uu___656_65647.wl_deferred);
                        ctr = (uu___656_65647.ctr);
                        defer_ok = (uu___656_65647.defer_ok);
                        smt_ok = (uu___656_65647.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_65647.umax_heuristic_ok);
                        tcenv = (uu___656_65647.tcenv);
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
            let uu___662_65680 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_65680.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_65680.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_65680.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_65680.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_65680.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_65680.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_65680.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_65680.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_65680.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_65680.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_65680.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_65680.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_65680.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_65680.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_65680.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_65680.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_65680.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_65680.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_65680.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_65680.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_65680.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_65680.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_65680.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_65680.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_65680.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_65680.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_65680.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_65680.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_65680.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_65680.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_65680.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_65680.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_65680.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_65680.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_65680.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_65680.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_65680.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_65680.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_65680.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_65680.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_65680.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_65680.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____65682 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____65682 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____65725 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____65762 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____65796 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____65807 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____65818 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_65836  ->
    match uu___585_65836 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____65848 = FStar_Syntax_Util.head_and_args t  in
    match uu____65848 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____65911 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____65913 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____65928 =
                     let uu____65930 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____65930  in
                   FStar_Util.format1 "@<%s>" uu____65928
                in
             let uu____65934 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____65911 uu____65913 uu____65934
         | uu____65937 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_65949  ->
      match uu___586_65949 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____65954 =
            let uu____65958 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____65960 =
              let uu____65964 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____65966 =
                let uu____65970 =
                  let uu____65974 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____65974]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____65970
                 in
              uu____65964 :: uu____65966  in
            uu____65958 :: uu____65960  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____65954
      | FStar_TypeChecker_Common.CProb p ->
          let uu____65985 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____65987 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____65989 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____65985
            uu____65987 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____65989
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_66003  ->
      match uu___587_66003 with
      | UNIV (u,t) ->
          let x =
            let uu____66009 = FStar_Options.hide_uvar_nums ()  in
            if uu____66009
            then "?"
            else
              (let uu____66016 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____66016 FStar_Util.string_of_int)
             in
          let uu____66020 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____66020
      | TERM (u,t) ->
          let x =
            let uu____66027 = FStar_Options.hide_uvar_nums ()  in
            if uu____66027
            then "?"
            else
              (let uu____66034 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____66034 FStar_Util.string_of_int)
             in
          let uu____66038 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____66038
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____66057 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____66057 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____66078 =
      let uu____66082 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____66082
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____66078 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____66101 .
    (FStar_Syntax_Syntax.term * 'Auu____66101) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____66120 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____66141  ->
              match uu____66141 with
              | (x,uu____66148) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____66120 (FStar_String.concat " ")
  
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
        (let uu____66191 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____66191
         then
           let uu____66196 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____66196
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_66207  ->
    match uu___588_66207 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____66213 .
    'Auu____66213 FStar_TypeChecker_Common.problem ->
      'Auu____66213 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_66225 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_66225.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_66225.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_66225.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_66225.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_66225.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_66225.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_66225.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____66233 .
    'Auu____66233 FStar_TypeChecker_Common.problem ->
      'Auu____66233 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_66253  ->
    match uu___589_66253 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66259  -> FStar_TypeChecker_Common.TProb _66259)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66265  -> FStar_TypeChecker_Common.CProb _66265)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_66271  ->
    match uu___590_66271 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_66277 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_66277.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_66277.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_66277.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_66277.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_66277.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_66277.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_66277.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_66277.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_66277.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_66285 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_66285.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_66285.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_66285.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_66285.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_66285.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_66285.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_66285.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_66285.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_66285.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_66298  ->
      match uu___591_66298 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_66305  ->
    match uu___592_66305 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_66318  ->
    match uu___593_66318 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_66333  ->
    match uu___594_66333 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_66348  ->
    match uu___595_66348 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_66362  ->
    match uu___596_66362 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_66376  ->
    match uu___597_66376 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_66388  ->
    match uu___598_66388 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____66404 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____66404) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____66434 =
          let uu____66436 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66436  in
        if uu____66434
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____66473)::bs ->
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
          let uu____66520 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66544 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66544]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66520
      | FStar_TypeChecker_Common.CProb p ->
          let uu____66572 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66596 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66596]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66572
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____66643 =
          let uu____66645 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66645  in
        if uu____66643
        then ()
        else
          (let uu____66650 =
             let uu____66653 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____66653
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____66650 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____66702 =
          let uu____66704 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66704  in
        if uu____66702
        then ()
        else
          (let uu____66709 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____66709)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____66729 =
        let uu____66731 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____66731  in
      if uu____66729
      then ()
      else
        (let msgf m =
           let uu____66745 =
             let uu____66747 =
               let uu____66749 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____66749 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____66747  in
           Prims.op_Hat msg uu____66745  in
         (let uu____66754 = msgf "scope"  in
          let uu____66757 = p_scope prob  in
          def_scope_wf uu____66754 (p_loc prob) uu____66757);
         (let uu____66769 = msgf "guard"  in
          def_check_scoped uu____66769 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____66776 = msgf "lhs"  in
                def_check_scoped uu____66776 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66779 = msgf "rhs"  in
                def_check_scoped uu____66779 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____66786 = msgf "lhs"  in
                def_check_scoped_comp uu____66786 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66789 = msgf "rhs"  in
                def_check_scoped_comp uu____66789 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_66810 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_66810.wl_deferred);
          ctr = (uu___831_66810.ctr);
          defer_ok = (uu___831_66810.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_66810.umax_heuristic_ok);
          tcenv = (uu___831_66810.tcenv);
          wl_implicits = (uu___831_66810.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____66818 .
    FStar_TypeChecker_Env.env ->
      ('Auu____66818 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_66841 = empty_worklist env  in
      let uu____66842 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____66842;
        wl_deferred = (uu___835_66841.wl_deferred);
        ctr = (uu___835_66841.ctr);
        defer_ok = (uu___835_66841.defer_ok);
        smt_ok = (uu___835_66841.smt_ok);
        umax_heuristic_ok = (uu___835_66841.umax_heuristic_ok);
        tcenv = (uu___835_66841.tcenv);
        wl_implicits = (uu___835_66841.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_66865 = wl  in
        {
          attempting = (uu___840_66865.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_66865.ctr);
          defer_ok = (uu___840_66865.defer_ok);
          smt_ok = (uu___840_66865.smt_ok);
          umax_heuristic_ok = (uu___840_66865.umax_heuristic_ok);
          tcenv = (uu___840_66865.tcenv);
          wl_implicits = (uu___840_66865.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_66893 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_66893.wl_deferred);
         ctr = (uu___845_66893.ctr);
         defer_ok = (uu___845_66893.defer_ok);
         smt_ok = (uu___845_66893.smt_ok);
         umax_heuristic_ok = (uu___845_66893.umax_heuristic_ok);
         tcenv = (uu___845_66893.tcenv);
         wl_implicits = (uu___845_66893.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____66907 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____66907 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____66941 = FStar_Syntax_Util.type_u ()  in
            match uu____66941 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____66953 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____66953 with
                 | (uu____66971,tt,wl1) ->
                     let uu____66974 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____66974, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_66980  ->
    match uu___599_66980 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _66986  -> FStar_TypeChecker_Common.TProb _66986) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _66992  -> FStar_TypeChecker_Common.CProb _66992) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____67000 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____67000 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____67020  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____67117 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____67117 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____67117 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____67117 FStar_TypeChecker_Common.problem *
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
                        let uu____67204 =
                          let uu____67213 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67213]  in
                        FStar_List.append scope uu____67204
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____67256 =
                      let uu____67259 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____67259  in
                    FStar_List.append uu____67256
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____67278 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67278 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____67304 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67304;
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
                  (let uu____67378 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67378 with
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
                  (let uu____67466 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67466 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____67504 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____67504 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____67504 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____67504 FStar_TypeChecker_Common.problem *
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
                          let uu____67572 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67572]  in
                        let uu____67591 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____67591
                     in
                  let uu____67594 =
                    let uu____67601 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_67612 = wl  in
                       {
                         attempting = (uu___928_67612.attempting);
                         wl_deferred = (uu___928_67612.wl_deferred);
                         ctr = (uu___928_67612.ctr);
                         defer_ok = (uu___928_67612.defer_ok);
                         smt_ok = (uu___928_67612.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_67612.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_67612.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____67601
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67594 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____67630 =
                              let uu____67635 =
                                let uu____67636 =
                                  let uu____67645 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____67645
                                   in
                                [uu____67636]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____67635
                               in
                            uu____67630 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____67675 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67675;
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
                let uu____67723 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____67723;
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
  'Auu____67738 .
    worklist ->
      'Auu____67738 FStar_TypeChecker_Common.problem ->
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
              let uu____67771 =
                let uu____67774 =
                  let uu____67775 =
                    let uu____67782 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____67782)  in
                  FStar_Syntax_Syntax.NT uu____67775  in
                [uu____67774]  in
              FStar_Syntax_Subst.subst uu____67771 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____67806 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____67806
        then
          let uu____67814 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____67817 = prob_to_string env d  in
          let uu____67819 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____67814 uu____67817 uu____67819 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____67835 -> failwith "impossible"  in
           let uu____67838 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____67854 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67856 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67854, uu____67856)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____67863 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67865 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67863, uu____67865)
              in
           match uu____67838 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_67893  ->
            match uu___600_67893 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____67905 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____67909 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____67909 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_67940  ->
           match uu___601_67940 with
           | UNIV uu____67943 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____67950 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____67950
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
        (fun uu___602_67978  ->
           match uu___602_67978 with
           | UNIV (u',t) ->
               let uu____67983 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____67983
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____67990 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____68002 =
        let uu____68003 =
          let uu____68004 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____68004
           in
        FStar_Syntax_Subst.compress uu____68003  in
      FStar_All.pipe_right uu____68002 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____68016 =
        let uu____68017 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____68017  in
      FStar_All.pipe_right uu____68016 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____68025 = FStar_Syntax_Util.head_and_args t  in
    match uu____68025 with
    | (h,uu____68044) ->
        let uu____68069 =
          let uu____68070 = FStar_Syntax_Subst.compress h  in
          uu____68070.FStar_Syntax_Syntax.n  in
        (match uu____68069 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____68075 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____68088 = should_strongly_reduce t  in
      if uu____68088
      then
        let uu____68091 =
          let uu____68092 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____68092  in
        FStar_All.pipe_right uu____68091 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____68102 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____68102) ->
        (FStar_Syntax_Syntax.term * 'Auu____68102)
  =
  fun env  ->
    fun t  ->
      let uu____68125 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____68125, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____68177  ->
              match uu____68177 with
              | (x,imp) ->
                  let uu____68196 =
                    let uu___1025_68197 = x  in
                    let uu____68198 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_68197.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_68197.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____68198
                    }  in
                  (uu____68196, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____68222 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____68222
        | FStar_Syntax_Syntax.U_max us ->
            let uu____68226 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____68226
        | uu____68229 -> u2  in
      let uu____68230 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____68230
  
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
                (let uu____68351 = norm_refinement env t12  in
                 match uu____68351 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____68366;
                     FStar_Syntax_Syntax.vars = uu____68367;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____68391 =
                       let uu____68393 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____68395 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____68393 uu____68395
                        in
                     failwith uu____68391)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____68411 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____68411
          | FStar_Syntax_Syntax.Tm_uinst uu____68412 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68449 =
                   let uu____68450 = FStar_Syntax_Subst.compress t1'  in
                   uu____68450.FStar_Syntax_Syntax.n  in
                 match uu____68449 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68465 -> aux true t1'
                 | uu____68473 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____68488 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68519 =
                   let uu____68520 = FStar_Syntax_Subst.compress t1'  in
                   uu____68520.FStar_Syntax_Syntax.n  in
                 match uu____68519 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68535 -> aux true t1'
                 | uu____68543 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____68558 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68605 =
                   let uu____68606 = FStar_Syntax_Subst.compress t1'  in
                   uu____68606.FStar_Syntax_Syntax.n  in
                 match uu____68605 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68621 -> aux true t1'
                 | uu____68629 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____68644 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____68659 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____68674 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____68689 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____68704 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____68733 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____68766 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____68787 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____68814 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____68842 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____68879 ->
              let uu____68886 =
                let uu____68888 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68890 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68888 uu____68890
                 in
              failwith uu____68886
          | FStar_Syntax_Syntax.Tm_ascribed uu____68905 ->
              let uu____68932 =
                let uu____68934 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68936 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68934 uu____68936
                 in
              failwith uu____68932
          | FStar_Syntax_Syntax.Tm_delayed uu____68951 ->
              let uu____68974 =
                let uu____68976 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68978 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68976 uu____68978
                 in
              failwith uu____68974
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____68993 =
                let uu____68995 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68997 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68995 uu____68997
                 in
              failwith uu____68993
           in
        let uu____69012 = whnf env t1  in aux false uu____69012
  
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
      let uu____69073 = base_and_refinement env t  in
      FStar_All.pipe_right uu____69073 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____69114 = FStar_Syntax_Syntax.null_bv t  in
    (uu____69114, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____69141 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____69141 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____69201  ->
    match uu____69201 with
    | (t_base,refopt) ->
        let uu____69232 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____69232 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____69274 =
      let uu____69278 =
        let uu____69281 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____69308  ->
                  match uu____69308 with | (uu____69317,uu____69318,x) -> x))
           in
        FStar_List.append wl.attempting uu____69281  in
      FStar_List.map (wl_prob_to_string wl) uu____69278  in
    FStar_All.pipe_right uu____69274 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____69341 .
    ('Auu____69341 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____69353  ->
    match uu____69353 with
    | (uu____69360,c,args) ->
        let uu____69363 = print_ctx_uvar c  in
        let uu____69365 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____69363 uu____69365
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____69375 = FStar_Syntax_Util.head_and_args t  in
    match uu____69375 with
    | (head1,_args) ->
        let uu____69419 =
          let uu____69420 = FStar_Syntax_Subst.compress head1  in
          uu____69420.FStar_Syntax_Syntax.n  in
        (match uu____69419 with
         | FStar_Syntax_Syntax.Tm_uvar uu____69424 -> true
         | uu____69438 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____69446 = FStar_Syntax_Util.head_and_args t  in
    match uu____69446 with
    | (head1,_args) ->
        let uu____69489 =
          let uu____69490 = FStar_Syntax_Subst.compress head1  in
          uu____69490.FStar_Syntax_Syntax.n  in
        (match uu____69489 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____69494) -> u
         | uu____69511 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____69536 = FStar_Syntax_Util.head_and_args t  in
      match uu____69536 with
      | (head1,args) ->
          let uu____69583 =
            let uu____69584 = FStar_Syntax_Subst.compress head1  in
            uu____69584.FStar_Syntax_Syntax.n  in
          (match uu____69583 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____69592)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____69625 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_69650  ->
                         match uu___603_69650 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____69655 =
                               let uu____69656 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____69656.FStar_Syntax_Syntax.n  in
                             (match uu____69655 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____69661 -> false)
                         | uu____69663 -> true))
                  in
               (match uu____69625 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____69688 =
                        FStar_List.collect
                          (fun uu___604_69700  ->
                             match uu___604_69700 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____69704 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____69704]
                             | uu____69705 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____69688 FStar_List.rev  in
                    let uu____69728 =
                      let uu____69735 =
                        let uu____69744 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_69766  ->
                                  match uu___605_69766 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____69770 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____69770]
                                  | uu____69771 -> []))
                           in
                        FStar_All.pipe_right uu____69744 FStar_List.rev  in
                      let uu____69794 =
                        let uu____69797 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____69797  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____69735 uu____69794
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____69728 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____69833  ->
                                match uu____69833 with
                                | (x,i) ->
                                    let uu____69852 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____69852, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____69883  ->
                                match uu____69883 with
                                | (a,i) ->
                                    let uu____69902 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____69902, i)) args_sol
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
           | uu____69924 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____69946 =
          let uu____69969 =
            let uu____69970 = FStar_Syntax_Subst.compress k  in
            uu____69970.FStar_Syntax_Syntax.n  in
          match uu____69969 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____70052 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____70052)
              else
                (let uu____70087 = FStar_Syntax_Util.abs_formals t  in
                 match uu____70087 with
                 | (ys',t1,uu____70120) ->
                     let uu____70125 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____70125))
          | uu____70164 ->
              let uu____70165 =
                let uu____70170 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____70170)  in
              ((ys, t), uu____70165)
           in
        match uu____69946 with
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
                 let uu____70265 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____70265 c  in
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
               (let uu____70343 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70343
                then
                  let uu____70348 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____70350 = print_ctx_uvar uv  in
                  let uu____70352 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____70348 uu____70350 uu____70352
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____70361 =
                   let uu____70363 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____70363  in
                 let uu____70366 =
                   let uu____70369 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____70369
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____70361 uu____70366 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____70402 =
               let uu____70403 =
                 let uu____70405 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____70407 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____70405 uu____70407
                  in
               failwith uu____70403  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____70473  ->
                       match uu____70473 with
                       | (a,i) ->
                           let uu____70494 =
                             let uu____70495 = FStar_Syntax_Subst.compress a
                                in
                             uu____70495.FStar_Syntax_Syntax.n  in
                           (match uu____70494 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____70521 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____70531 =
                 let uu____70533 = is_flex g  in
                 Prims.op_Negation uu____70533  in
               if uu____70531
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____70542 = destruct_flex_t g wl  in
                  match uu____70542 with
                  | ((uu____70547,uv1,args),wl1) ->
                      ((let uu____70552 = args_as_binders args  in
                        assign_solution uu____70552 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_70554 = wl1  in
              {
                attempting = (uu___1277_70554.attempting);
                wl_deferred = (uu___1277_70554.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_70554.defer_ok);
                smt_ok = (uu___1277_70554.smt_ok);
                umax_heuristic_ok = (uu___1277_70554.umax_heuristic_ok);
                tcenv = (uu___1277_70554.tcenv);
                wl_implicits = (uu___1277_70554.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____70579 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____70579
         then
           let uu____70584 = FStar_Util.string_of_int pid  in
           let uu____70586 =
             let uu____70588 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____70588 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____70584
             uu____70586
         else ());
        commit sol;
        (let uu___1285_70602 = wl  in
         {
           attempting = (uu___1285_70602.attempting);
           wl_deferred = (uu___1285_70602.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_70602.defer_ok);
           smt_ok = (uu___1285_70602.smt_ok);
           umax_heuristic_ok = (uu___1285_70602.umax_heuristic_ok);
           tcenv = (uu___1285_70602.tcenv);
           wl_implicits = (uu___1285_70602.wl_implicits)
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
             | (uu____70668,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____70696 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____70696
              in
           (let uu____70702 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____70702
            then
              let uu____70707 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____70711 =
                let uu____70713 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____70713 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____70707
                uu____70711
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
        let uu____70748 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____70748 FStar_Util.set_elements  in
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
      let uu____70788 = occurs uk t  in
      match uu____70788 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____70827 =
                 let uu____70829 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____70831 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____70829 uu____70831
                  in
               FStar_Pervasives_Native.Some uu____70827)
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
            let uu____70951 = maximal_prefix bs_tail bs'_tail  in
            (match uu____70951 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____71002 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____71059  ->
             match uu____71059 with
             | (x,uu____71071) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____71089 = FStar_List.last bs  in
      match uu____71089 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____71113) ->
          let uu____71124 =
            FStar_Util.prefix_until
              (fun uu___606_71139  ->
                 match uu___606_71139 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____71142 -> false) g
             in
          (match uu____71124 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____71156,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____71193 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____71193 with
        | (pfx,uu____71203) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____71215 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____71215 with
             | (uu____71223,src',wl1) ->
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
                 | uu____71337 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____71338 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____71402  ->
                  fun uu____71403  ->
                    match (uu____71402, uu____71403) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____71506 =
                          let uu____71508 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____71508
                           in
                        if uu____71506
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____71542 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____71542
                           then
                             let uu____71559 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____71559)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____71338 with | (isect,uu____71609) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____71645 'Auu____71646 .
    (FStar_Syntax_Syntax.bv * 'Auu____71645) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____71646) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____71704  ->
              fun uu____71705  ->
                match (uu____71704, uu____71705) with
                | ((a,uu____71724),(b,uu____71726)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____71742 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____71742) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____71773  ->
           match uu____71773 with
           | (y,uu____71780) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____71790 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____71790) Prims.list ->
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
                   let uu____71952 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____71952
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____71985 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____72037 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____72082 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____72104 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_72112  ->
    match uu___607_72112 with
    | MisMatch (d1,d2) ->
        let uu____72124 =
          let uu____72126 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____72128 =
            let uu____72130 =
              let uu____72132 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____72132 ")"  in
            Prims.op_Hat ") (" uu____72130  in
          Prims.op_Hat uu____72126 uu____72128  in
        Prims.op_Hat "MisMatch (" uu____72124
    | HeadMatch u ->
        let uu____72139 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____72139
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_72148  ->
    match uu___608_72148 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____72165 -> HeadMatch false
  
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
          let uu____72187 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____72187 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____72198 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____72222 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____72232 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____72259 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____72259
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____72260 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____72261 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____72262 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____72275 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____72289 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____72313) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72319,uu____72320) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____72362) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____72387;
             FStar_Syntax_Syntax.index = uu____72388;
             FStar_Syntax_Syntax.sort = t2;_},uu____72390)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____72398 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____72399 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____72400 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____72415 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____72422 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____72442 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____72442
  
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
           { FStar_Syntax_Syntax.blob = uu____72461;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72462;
             FStar_Syntax_Syntax.ltyp = uu____72463;
             FStar_Syntax_Syntax.rng = uu____72464;_},uu____72465)
            ->
            let uu____72476 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____72476 t21
        | (uu____72477,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____72478;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72479;
             FStar_Syntax_Syntax.ltyp = uu____72480;
             FStar_Syntax_Syntax.rng = uu____72481;_})
            ->
            let uu____72492 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____72492
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____72504 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____72504
            then FullMatch
            else
              (let uu____72509 =
                 let uu____72518 =
                   let uu____72521 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____72521  in
                 let uu____72522 =
                   let uu____72525 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____72525  in
                 (uu____72518, uu____72522)  in
               MisMatch uu____72509)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____72531),FStar_Syntax_Syntax.Tm_uinst (g,uu____72533)) ->
            let uu____72542 = head_matches env f g  in
            FStar_All.pipe_right uu____72542 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____72543) -> HeadMatch true
        | (uu____72545,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____72549 = FStar_Const.eq_const c d  in
            if uu____72549
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____72559),FStar_Syntax_Syntax.Tm_uvar (uv',uu____72561)) ->
            let uu____72594 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____72594
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____72604),FStar_Syntax_Syntax.Tm_refine (y,uu____72606)) ->
            let uu____72615 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72615 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____72617),uu____72618) ->
            let uu____72623 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____72623 head_match
        | (uu____72624,FStar_Syntax_Syntax.Tm_refine (x,uu____72626)) ->
            let uu____72631 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72631 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____72632,FStar_Syntax_Syntax.Tm_type uu____72633) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____72635,FStar_Syntax_Syntax.Tm_arrow uu____72636) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____72667),FStar_Syntax_Syntax.Tm_app
           (head',uu____72669)) ->
            let uu____72718 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____72718 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____72720),uu____72721) ->
            let uu____72746 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____72746 head_match
        | (uu____72747,FStar_Syntax_Syntax.Tm_app (head1,uu____72749)) ->
            let uu____72774 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____72774 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____72775,FStar_Syntax_Syntax.Tm_let
           uu____72776) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____72804,FStar_Syntax_Syntax.Tm_match uu____72805) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____72851,FStar_Syntax_Syntax.Tm_abs
           uu____72852) -> HeadMatch true
        | uu____72890 ->
            let uu____72895 =
              let uu____72904 = delta_depth_of_term env t11  in
              let uu____72907 = delta_depth_of_term env t21  in
              (uu____72904, uu____72907)  in
            MisMatch uu____72895
  
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
            (let uu____72973 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____72973
             then
               let uu____72978 = FStar_Syntax_Print.term_to_string t  in
               let uu____72980 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____72978 uu____72980
             else ());
            (let uu____72985 =
               let uu____72986 = FStar_Syntax_Util.un_uinst head1  in
               uu____72986.FStar_Syntax_Syntax.n  in
             match uu____72985 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72992 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____72992 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____73006 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____73006
                        then
                          let uu____73011 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____73011
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____73016 ->
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
                      let uu____73033 =
                        let uu____73035 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____73035 = FStar_Syntax_Util.Equal  in
                      if uu____73033
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____73042 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____73042
                          then
                            let uu____73047 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____73049 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____73047 uu____73049
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____73054 -> FStar_Pervasives_Native.None)
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
            (let uu____73206 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____73206
             then
               let uu____73211 = FStar_Syntax_Print.term_to_string t11  in
               let uu____73213 = FStar_Syntax_Print.term_to_string t21  in
               let uu____73215 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____73211
                 uu____73213 uu____73215
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____73243 =
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
               match uu____73243 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____73291 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____73291 with
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
                  uu____73329),uu____73330)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73351 =
                      let uu____73360 = maybe_inline t11  in
                      let uu____73363 = maybe_inline t21  in
                      (uu____73360, uu____73363)  in
                    match uu____73351 with
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
                 (uu____73406,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____73407))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73428 =
                      let uu____73437 = maybe_inline t11  in
                      let uu____73440 = maybe_inline t21  in
                      (uu____73437, uu____73440)  in
                    match uu____73428 with
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
             | MisMatch uu____73495 -> fail1 n_delta r t11 t21
             | uu____73504 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____73519 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____73519
           then
             let uu____73524 = FStar_Syntax_Print.term_to_string t1  in
             let uu____73526 = FStar_Syntax_Print.term_to_string t2  in
             let uu____73528 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____73536 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____73553 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____73553
                    (fun uu____73588  ->
                       match uu____73588 with
                       | (t11,t21) ->
                           let uu____73596 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____73598 =
                             let uu____73600 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____73600  in
                           Prims.op_Hat uu____73596 uu____73598))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____73524 uu____73526 uu____73528 uu____73536
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____73617 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____73617 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_73632  ->
    match uu___609_73632 with
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
      let uu___1789_73681 = p  in
      let uu____73684 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____73685 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_73681.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____73684;
        FStar_TypeChecker_Common.relation =
          (uu___1789_73681.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____73685;
        FStar_TypeChecker_Common.element =
          (uu___1789_73681.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_73681.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_73681.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_73681.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_73681.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_73681.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____73700 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____73700
            (fun _73705  -> FStar_TypeChecker_Common.TProb _73705)
      | FStar_TypeChecker_Common.CProb uu____73706 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____73729 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____73729 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____73737 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____73737 with
           | (lh,lhs_args) ->
               let uu____73784 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____73784 with
                | (rh,rhs_args) ->
                    let uu____73831 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73844,FStar_Syntax_Syntax.Tm_uvar uu____73845)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____73934 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____73961,uu____73962)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____73977,FStar_Syntax_Syntax.Tm_uvar uu____73978)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73993,FStar_Syntax_Syntax.Tm_arrow
                         uu____73994) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74024 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74024.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74024.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74024.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74024.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74024.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74024.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74024.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74024.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74024.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____74027,FStar_Syntax_Syntax.Tm_type uu____74028)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74044 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74044.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74044.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74044.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74044.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74044.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74044.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74044.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74044.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74044.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____74047,FStar_Syntax_Syntax.Tm_uvar uu____74048)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_74064 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_74064.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_74064.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_74064.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_74064.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_74064.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_74064.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_74064.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_74064.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_74064.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____74067,FStar_Syntax_Syntax.Tm_uvar uu____74068)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____74083,uu____74084)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____74099,FStar_Syntax_Syntax.Tm_uvar uu____74100)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____74115,uu____74116) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____73831 with
                     | (rank,tp1) ->
                         let uu____74129 =
                           FStar_All.pipe_right
                             (let uu___1860_74133 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_74133.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_74133.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_74133.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_74133.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_74133.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_74133.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_74133.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_74133.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_74133.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _74136  ->
                                FStar_TypeChecker_Common.TProb _74136)
                            in
                         (rank, uu____74129))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____74140 =
            FStar_All.pipe_right
              (let uu___1864_74144 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_74144.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_74144.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_74144.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_74144.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_74144.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_74144.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_74144.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_74144.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_74144.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _74147  -> FStar_TypeChecker_Common.CProb _74147)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____74140)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____74207 probs =
      match uu____74207 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____74288 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____74309 = rank wl.tcenv hd1  in
               (match uu____74309 with
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
                      (let uu____74370 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____74375 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____74375)
                          in
                       if uu____74370
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
          let uu____74448 = FStar_Syntax_Util.head_and_args t  in
          match uu____74448 with
          | (hd1,uu____74467) ->
              let uu____74492 =
                let uu____74493 = FStar_Syntax_Subst.compress hd1  in
                uu____74493.FStar_Syntax_Syntax.n  in
              (match uu____74492 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____74498) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____74533  ->
                           match uu____74533 with
                           | (y,uu____74542) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____74565  ->
                                       match uu____74565 with
                                       | (x,uu____74574) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____74579 -> false)
           in
        let uu____74581 = rank tcenv p  in
        match uu____74581 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____74590 -> true
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
    match projectee with | UDeferred _0 -> true | uu____74627 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____74647 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____74668 -> false
  
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
                        let uu____74731 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____74731 with
                        | (k,uu____74739) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____74752 -> false)))
            | uu____74754 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____74806 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____74814 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____74814 = (Prims.parse_int "0")))
                           in
                        if uu____74806 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____74835 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____74843 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____74843 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____74835)
               in
            let uu____74847 = filter1 u12  in
            let uu____74850 = filter1 u22  in (uu____74847, uu____74850)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____74885 = filter_out_common_univs us1 us2  in
                   (match uu____74885 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____74945 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____74945 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____74948 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____74959 =
                             let uu____74961 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____74963 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____74961 uu____74963
                              in
                           UFailed uu____74959))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74989 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74989 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____75015 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____75015 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____75018 ->
                   let uu____75023 =
                     let uu____75025 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____75027 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____75025 uu____75027 msg
                      in
                   UFailed uu____75023)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____75030,uu____75031) ->
              let uu____75033 =
                let uu____75035 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75037 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75035 uu____75037
                 in
              failwith uu____75033
          | (FStar_Syntax_Syntax.U_unknown ,uu____75040) ->
              let uu____75041 =
                let uu____75043 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75045 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75043 uu____75045
                 in
              failwith uu____75041
          | (uu____75048,FStar_Syntax_Syntax.U_bvar uu____75049) ->
              let uu____75051 =
                let uu____75053 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75055 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75053 uu____75055
                 in
              failwith uu____75051
          | (uu____75058,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____75059 =
                let uu____75061 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____75063 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____75061 uu____75063
                 in
              failwith uu____75059
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____75093 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____75093
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____75110 = occurs_univ v1 u3  in
              if uu____75110
              then
                let uu____75113 =
                  let uu____75115 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75117 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75115 uu____75117
                   in
                try_umax_components u11 u21 uu____75113
              else
                (let uu____75122 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75122)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____75134 = occurs_univ v1 u3  in
              if uu____75134
              then
                let uu____75137 =
                  let uu____75139 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75141 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75139 uu____75141
                   in
                try_umax_components u11 u21 uu____75137
              else
                (let uu____75146 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75146)
          | (FStar_Syntax_Syntax.U_max uu____75147,uu____75148) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75156 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75156
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____75162,FStar_Syntax_Syntax.U_max uu____75163) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75171 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75171
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____75177,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____75179,FStar_Syntax_Syntax.U_name uu____75180) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____75182) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____75184) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75186,FStar_Syntax_Syntax.U_succ uu____75187) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75189,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____75296 = bc1  in
      match uu____75296 with
      | (bs1,mk_cod1) ->
          let uu____75340 = bc2  in
          (match uu____75340 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____75451 = aux xs ys  in
                     (match uu____75451 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____75534 =
                       let uu____75541 = mk_cod1 xs  in ([], uu____75541)  in
                     let uu____75544 =
                       let uu____75551 = mk_cod2 ys  in ([], uu____75551)  in
                     (uu____75534, uu____75544)
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
                  let uu____75620 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____75620 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____75623 =
                    let uu____75624 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____75624 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____75623
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____75629 = has_type_guard t1 t2  in (uu____75629, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____75630 = has_type_guard t2 t1  in (uu____75630, wl)
  
let is_flex_pat :
  'Auu____75640 'Auu____75641 'Auu____75642 .
    ('Auu____75640 * 'Auu____75641 * 'Auu____75642 Prims.list) -> Prims.bool
  =
  fun uu___610_75656  ->
    match uu___610_75656 with
    | (uu____75665,uu____75666,[]) -> true
    | uu____75670 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____75703 = f  in
      match uu____75703 with
      | (uu____75710,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____75711;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____75712;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____75715;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____75716;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____75717;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____75718;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____75788  ->
                 match uu____75788 with
                 | (y,uu____75797) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____75951 =
                  let uu____75966 =
                    let uu____75969 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____75969  in
                  ((FStar_List.rev pat_binders), uu____75966)  in
                FStar_Pervasives_Native.Some uu____75951
            | (uu____76002,[]) ->
                let uu____76033 =
                  let uu____76048 =
                    let uu____76051 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____76051  in
                  ((FStar_List.rev pat_binders), uu____76048)  in
                FStar_Pervasives_Native.Some uu____76033
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____76142 =
                  let uu____76143 = FStar_Syntax_Subst.compress a  in
                  uu____76143.FStar_Syntax_Syntax.n  in
                (match uu____76142 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____76163 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____76163
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_76193 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_76193.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_76193.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____76197 =
                            let uu____76198 =
                              let uu____76205 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____76205)  in
                            FStar_Syntax_Syntax.NT uu____76198  in
                          [uu____76197]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_76221 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_76221.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_76221.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____76222 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____76262 =
                  let uu____76277 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____76277  in
                (match uu____76262 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____76352 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____76385 ->
               let uu____76386 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____76386 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____76708 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____76708
       then
         let uu____76713 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____76713
       else ());
      (let uu____76718 = next_prob probs  in
       match uu____76718 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_76745 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_76745.wl_deferred);
               ctr = (uu___2219_76745.ctr);
               defer_ok = (uu___2219_76745.defer_ok);
               smt_ok = (uu___2219_76745.smt_ok);
               umax_heuristic_ok = (uu___2219_76745.umax_heuristic_ok);
               tcenv = (uu___2219_76745.tcenv);
               wl_implicits = (uu___2219_76745.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____76754 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____76754
                 then
                   let uu____76757 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____76757
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
                           (let uu___2231_76769 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_76769.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_76769.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_76769.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_76769.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_76769.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_76769.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_76769.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_76769.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_76769.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____76795 ->
                let uu____76806 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____76877  ->
                          match uu____76877 with
                          | (c,uu____76888,uu____76889) -> c < probs.ctr))
                   in
                (match uu____76806 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____76944 =
                            let uu____76949 =
                              FStar_List.map
                                (fun uu____76967  ->
                                   match uu____76967 with
                                   | (uu____76981,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____76949, (probs.wl_implicits))  in
                          Success uu____76944
                      | uu____76989 ->
                          let uu____77000 =
                            let uu___2249_77001 = probs  in
                            let uu____77002 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____77025  ->
                                      match uu____77025 with
                                      | (uu____77034,uu____77035,y) -> y))
                               in
                            {
                              attempting = uu____77002;
                              wl_deferred = rest;
                              ctr = (uu___2249_77001.ctr);
                              defer_ok = (uu___2249_77001.defer_ok);
                              smt_ok = (uu___2249_77001.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_77001.umax_heuristic_ok);
                              tcenv = (uu___2249_77001.tcenv);
                              wl_implicits = (uu___2249_77001.wl_implicits)
                            }  in
                          solve env uu____77000))))

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
            let uu____77046 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____77046 with
            | USolved wl1 ->
                let uu____77048 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____77048
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
                  let uu____77102 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____77102 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____77105 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____77118;
                  FStar_Syntax_Syntax.vars = uu____77119;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____77122;
                  FStar_Syntax_Syntax.vars = uu____77123;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____77136,uu____77137) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____77145,FStar_Syntax_Syntax.Tm_uinst uu____77146) ->
                failwith "Impossible: expect head symbols to match"
            | uu____77154 -> USolved wl

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
            ((let uu____77166 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____77166
              then
                let uu____77171 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____77171 msg
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
               let uu____77263 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____77263 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____77318 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____77318
                then
                  let uu____77323 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____77325 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____77323 uu____77325
                else ());
               (let uu____77330 = head_matches_delta env1 wl2 t1 t2  in
                match uu____77330 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____77376 = eq_prob t1 t2 wl2  in
                         (match uu____77376 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____77397 ->
                         let uu____77406 = eq_prob t1 t2 wl2  in
                         (match uu____77406 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____77456 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____77471 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____77472 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____77471, uu____77472)
                           | FStar_Pervasives_Native.None  ->
                               let uu____77477 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____77478 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____77477, uu____77478)
                            in
                         (match uu____77456 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____77509 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____77509 with
                                | (t1_hd,t1_args) ->
                                    let uu____77554 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____77554 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____77620 =
                                              let uu____77627 =
                                                let uu____77638 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____77638 :: t1_args  in
                                              let uu____77655 =
                                                let uu____77664 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____77664 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____77713  ->
                                                   fun uu____77714  ->
                                                     fun uu____77715  ->
                                                       match (uu____77713,
                                                               uu____77714,
                                                               uu____77715)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____77765),
                                                          (a2,uu____77767))
                                                           ->
                                                           let uu____77804 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____77804
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____77627
                                                uu____77655
                                               in
                                            match uu____77620 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_77830 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_77830.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_77830.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_77830.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____77842 =
                                                  solve env1 wl'  in
                                                (match uu____77842 with
                                                 | Success (uu____77845,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_77849
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_77849.attempting);
                                                            wl_deferred =
                                                              (uu___2412_77849.wl_deferred);
                                                            ctr =
                                                              (uu___2412_77849.ctr);
                                                            defer_ok =
                                                              (uu___2412_77849.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_77849.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_77849.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_77849.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____77850 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____77883 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____77883 with
                                | (t1_base,p1_opt) ->
                                    let uu____77919 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____77919 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____78018 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____78018
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
                                               let uu____78071 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____78071
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
                                               let uu____78103 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78103
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
                                               let uu____78135 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78135
                                           | uu____78138 -> t_base  in
                                         let uu____78155 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____78155 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____78169 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____78169, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____78176 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____78176 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____78212 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____78212 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____78248 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____78248
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
                              let uu____78272 = combine t11 t21 wl2  in
                              (match uu____78272 with
                               | (t12,ps,wl3) ->
                                   ((let uu____78305 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____78305
                                     then
                                       let uu____78310 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____78310
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____78352 ts1 =
               match uu____78352 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____78415 = pairwise out t wl2  in
                        (match uu____78415 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____78451 =
               let uu____78462 = FStar_List.hd ts  in (uu____78462, [], wl1)
                in
             let uu____78471 = FStar_List.tl ts  in
             aux uu____78451 uu____78471  in
           let uu____78478 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____78478 with
           | (this_flex,this_rigid) ->
               let uu____78504 =
                 let uu____78505 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____78505.FStar_Syntax_Syntax.n  in
               (match uu____78504 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____78530 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____78530
                    then
                      let uu____78533 = destruct_flex_t this_flex wl  in
                      (match uu____78533 with
                       | (flex,wl1) ->
                           let uu____78540 = quasi_pattern env flex  in
                           (match uu____78540 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____78559 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____78559
                                  then
                                    let uu____78564 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____78564
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____78571 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_78574 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_78574.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_78574.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_78574.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_78574.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_78574.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_78574.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_78574.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_78574.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_78574.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____78571)
                | uu____78575 ->
                    ((let uu____78577 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____78577
                      then
                        let uu____78582 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____78582
                      else ());
                     (let uu____78587 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____78587 with
                      | (u,_args) ->
                          let uu____78630 =
                            let uu____78631 = FStar_Syntax_Subst.compress u
                               in
                            uu____78631.FStar_Syntax_Syntax.n  in
                          (match uu____78630 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____78659 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____78659 with
                                 | (u',uu____78678) ->
                                     let uu____78703 =
                                       let uu____78704 = whnf env u'  in
                                       uu____78704.FStar_Syntax_Syntax.n  in
                                     (match uu____78703 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____78726 -> false)
                                  in
                               let uu____78728 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_78751  ->
                                         match uu___611_78751 with
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
                                              | uu____78765 -> false)
                                         | uu____78769 -> false))
                                  in
                               (match uu____78728 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____78784 = whnf env this_rigid
                                         in
                                      let uu____78785 =
                                        FStar_List.collect
                                          (fun uu___612_78791  ->
                                             match uu___612_78791 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____78797 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____78797]
                                             | uu____78801 -> [])
                                          bounds_probs
                                         in
                                      uu____78784 :: uu____78785  in
                                    let uu____78802 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____78802 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____78835 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____78850 =
                                               let uu____78851 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____78851.FStar_Syntax_Syntax.n
                                                in
                                             match uu____78850 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____78863 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____78863)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____78874 -> bound  in
                                           let uu____78875 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____78875)  in
                                         (match uu____78835 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____78910 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____78910
                                                then
                                                  let wl'1 =
                                                    let uu___2574_78916 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_78916.wl_deferred);
                                                      ctr =
                                                        (uu___2574_78916.ctr);
                                                      defer_ok =
                                                        (uu___2574_78916.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_78916.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_78916.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_78916.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_78916.wl_implicits)
                                                    }  in
                                                  let uu____78917 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____78917
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____78923 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_78925 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_78925.wl_deferred);
                                                       ctr =
                                                         (uu___2579_78925.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_78925.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_78925.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_78925.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____78923 with
                                                | Success (uu____78927,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_78930 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_78930.wl_deferred);
                                                        ctr =
                                                          (uu___2585_78930.ctr);
                                                        defer_ok =
                                                          (uu___2585_78930.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_78930.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_78930.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_78930.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_78930.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_78932 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_78932.attempting);
                                                        wl_deferred =
                                                          (uu___2588_78932.wl_deferred);
                                                        ctr =
                                                          (uu___2588_78932.ctr);
                                                        defer_ok =
                                                          (uu___2588_78932.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_78932.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_78932.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_78932.tcenv);
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
                                                    let uu____78948 =
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
                                                    ((let uu____78962 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____78962
                                                      then
                                                        let uu____78967 =
                                                          let uu____78969 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____78969
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____78967
                                                      else ());
                                                     (let uu____78982 =
                                                        let uu____78997 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____78997)
                                                         in
                                                      match uu____78982 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____79019))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____79045 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____79045
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
                                                                  let uu____79065
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79065))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____79090 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____79090
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
                                                                    let uu____79110
                                                                    =
                                                                    let uu____79115
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79115
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____79110
                                                                    [] wl2
                                                                     in
                                                                  let uu____79121
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79121))))
                                                      | uu____79122 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____79138 when flip ->
                               let uu____79139 =
                                 let uu____79141 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79143 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____79141 uu____79143
                                  in
                               failwith uu____79139
                           | uu____79146 ->
                               let uu____79147 =
                                 let uu____79149 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79151 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____79149 uu____79151
                                  in
                               failwith uu____79147)))))

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
                      (fun uu____79187  ->
                         match uu____79187 with
                         | (x,i) ->
                             let uu____79206 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____79206, i)) bs_lhs
                     in
                  let uu____79209 = lhs  in
                  match uu____79209 with
                  | (uu____79210,u_lhs,uu____79212) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____79309 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____79319 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____79319, univ)
                             in
                          match uu____79309 with
                          | (k,univ) ->
                              let uu____79326 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____79326 with
                               | (uu____79343,u,wl3) ->
                                   let uu____79346 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____79346, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____79372 =
                              let uu____79385 =
                                let uu____79396 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____79396 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____79447  ->
                                   fun uu____79448  ->
                                     match (uu____79447, uu____79448) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____79549 =
                                           let uu____79556 =
                                             let uu____79559 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____79559
                                              in
                                           copy_uvar u_lhs [] uu____79556 wl2
                                            in
                                         (match uu____79549 with
                                          | (uu____79588,t_a,wl3) ->
                                              let uu____79591 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____79591 with
                                               | (uu____79610,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____79385
                                ([], wl1)
                               in
                            (match uu____79372 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_79666 = ct  in
                                   let uu____79667 =
                                     let uu____79670 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____79670
                                      in
                                   let uu____79685 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_79666.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_79666.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____79667;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____79685;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_79666.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_79703 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_79703.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_79703.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____79706 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____79706 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____79768 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____79768 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____79779 =
                                          let uu____79784 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____79784)  in
                                        TERM uu____79779  in
                                      let uu____79785 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____79785 with
                                       | (sub_prob,wl3) ->
                                           let uu____79799 =
                                             let uu____79800 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____79800
                                              in
                                           solve env uu____79799))
                             | (x,imp)::formals2 ->
                                 let uu____79822 =
                                   let uu____79829 =
                                     let uu____79832 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____79832
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____79829 wl1
                                    in
                                 (match uu____79822 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____79853 =
                                          let uu____79856 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____79856
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____79853 u_x
                                         in
                                      let uu____79857 =
                                        let uu____79860 =
                                          let uu____79863 =
                                            let uu____79864 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____79864, imp)  in
                                          [uu____79863]  in
                                        FStar_List.append bs_terms
                                          uu____79860
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____79857 formals2 wl2)
                              in
                           let uu____79891 = occurs_check u_lhs arrow1  in
                           (match uu____79891 with
                            | (uu____79904,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____79920 =
                                    let uu____79922 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____79922
                                     in
                                  giveup_or_defer env orig wl uu____79920
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
              (let uu____79955 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____79955
               then
                 let uu____79960 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____79963 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____79960 (rel_to_string (p_rel orig)) uu____79963
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____80090 = rhs wl1 scope env1 subst1  in
                     (match uu____80090 with
                      | (rhs_prob,wl2) ->
                          ((let uu____80111 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____80111
                            then
                              let uu____80116 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____80116
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____80194 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____80194 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_80196 = hd1  in
                       let uu____80197 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_80196.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_80196.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80197
                       }  in
                     let hd21 =
                       let uu___2773_80201 = hd2  in
                       let uu____80202 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_80201.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_80201.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80202
                       }  in
                     let uu____80205 =
                       let uu____80210 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____80210
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____80205 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____80231 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____80231
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____80238 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____80238 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____80305 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____80305
                                  in
                               ((let uu____80323 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____80323
                                 then
                                   let uu____80328 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____80330 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____80328
                                     uu____80330
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____80363 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____80399 = aux wl [] env [] bs1 bs2  in
               match uu____80399 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____80454 = attempt sub_probs wl2  in
                   solve env uu____80454)

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
            let uu___2808_80475 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_80475.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_80475.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____80488 = try_solve env wl'  in
          match uu____80488 with
          | Success (uu____80489,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_80493 = wl  in
                  {
                    attempting = (uu___2817_80493.attempting);
                    wl_deferred = (uu___2817_80493.wl_deferred);
                    ctr = (uu___2817_80493.ctr);
                    defer_ok = (uu___2817_80493.defer_ok);
                    smt_ok = (uu___2817_80493.smt_ok);
                    umax_heuristic_ok = (uu___2817_80493.umax_heuristic_ok);
                    tcenv = (uu___2817_80493.tcenv);
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
        (let uu____80505 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____80505 wl)

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
              let uu____80519 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____80519 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____80553 = lhs1  in
              match uu____80553 with
              | (uu____80556,ctx_u,uu____80558) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____80566 ->
                        let uu____80567 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____80567 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____80616 = quasi_pattern env1 lhs1  in
              match uu____80616 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____80650) ->
                  let uu____80655 = lhs1  in
                  (match uu____80655 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____80670 = occurs_check ctx_u rhs1  in
                       (match uu____80670 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____80721 =
                                let uu____80729 =
                                  let uu____80731 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____80731
                                   in
                                FStar_Util.Inl uu____80729  in
                              (uu____80721, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____80759 =
                                 let uu____80761 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____80761  in
                               if uu____80759
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____80788 =
                                    let uu____80796 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____80796  in
                                  let uu____80802 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____80788, uu____80802)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____80846 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____80846 with
              | (rhs_hd,args) ->
                  let uu____80889 = FStar_Util.prefix args  in
                  (match uu____80889 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____80961 = lhs1  in
                       (match uu____80961 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____80965 =
                              let uu____80976 =
                                let uu____80983 =
                                  let uu____80986 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____80986
                                   in
                                copy_uvar u_lhs [] uu____80983 wl1  in
                              match uu____80976 with
                              | (uu____81013,t_last_arg,wl2) ->
                                  let uu____81016 =
                                    let uu____81023 =
                                      let uu____81024 =
                                        let uu____81033 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____81033]  in
                                      FStar_List.append bs_lhs uu____81024
                                       in
                                    copy_uvar u_lhs uu____81023 t_res_lhs wl2
                                     in
                                  (match uu____81016 with
                                   | (uu____81068,lhs',wl3) ->
                                       let uu____81071 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____81071 with
                                        | (uu____81088,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____80965 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____81109 =
                                     let uu____81110 =
                                       let uu____81115 =
                                         let uu____81116 =
                                           let uu____81119 =
                                             let uu____81124 =
                                               let uu____81125 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____81125]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____81124
                                              in
                                           uu____81119
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____81116
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____81115)  in
                                     TERM uu____81110  in
                                   [uu____81109]  in
                                 let uu____81152 =
                                   let uu____81159 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____81159 with
                                   | (p1,wl3) ->
                                       let uu____81179 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____81179 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____81152 with
                                  | (sub_probs,wl3) ->
                                      let uu____81211 =
                                        let uu____81212 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____81212  in
                                      solve env1 uu____81211))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____81246 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____81246 with
                | (uu____81264,args) ->
                    (match args with | [] -> false | uu____81300 -> true)
                 in
              let is_arrow rhs2 =
                let uu____81319 =
                  let uu____81320 = FStar_Syntax_Subst.compress rhs2  in
                  uu____81320.FStar_Syntax_Syntax.n  in
                match uu____81319 with
                | FStar_Syntax_Syntax.Tm_arrow uu____81324 -> true
                | uu____81340 -> false  in
              let uu____81342 = quasi_pattern env1 lhs1  in
              match uu____81342 with
              | FStar_Pervasives_Native.None  ->
                  let uu____81353 =
                    let uu____81355 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____81355
                     in
                  giveup_or_defer env1 orig1 wl1 uu____81353
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____81364 = is_app rhs1  in
                  if uu____81364
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____81369 = is_arrow rhs1  in
                     if uu____81369
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____81374 =
                          let uu____81376 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____81376
                           in
                        giveup_or_defer env1 orig1 wl1 uu____81374))
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
                let uu____81387 = lhs  in
                (match uu____81387 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____81391 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____81391 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____81409 =
                              let uu____81413 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____81413
                               in
                            FStar_All.pipe_right uu____81409
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____81434 = occurs_check ctx_uv rhs1  in
                          (match uu____81434 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____81463 =
                                   let uu____81465 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____81465
                                    in
                                 giveup_or_defer env orig wl uu____81463
                               else
                                 (let uu____81471 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____81471
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____81478 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____81478
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____81482 =
                                         let uu____81484 =
                                           names_to_string1 fvs2  in
                                         let uu____81486 =
                                           names_to_string1 fvs1  in
                                         let uu____81488 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____81484 uu____81486
                                           uu____81488
                                          in
                                       giveup_or_defer env orig wl
                                         uu____81482)
                                    else first_order orig env wl lhs rhs1))
                      | uu____81500 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____81507 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____81507 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____81533 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____81533
                             | (FStar_Util.Inl msg,uu____81535) ->
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
                  (let uu____81580 =
                     let uu____81597 = quasi_pattern env lhs  in
                     let uu____81604 = quasi_pattern env rhs  in
                     (uu____81597, uu____81604)  in
                   match uu____81580 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____81647 = lhs  in
                       (match uu____81647 with
                        | ({ FStar_Syntax_Syntax.n = uu____81648;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____81650;_},u_lhs,uu____81652)
                            ->
                            let uu____81655 = rhs  in
                            (match uu____81655 with
                             | (uu____81656,u_rhs,uu____81658) ->
                                 let uu____81659 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____81659
                                 then
                                   let uu____81666 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____81666
                                 else
                                   (let uu____81669 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____81669 with
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
                                        let uu____81701 =
                                          let uu____81708 =
                                            let uu____81711 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____81711
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____81708
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____81701 with
                                         | (uu____81723,w,wl1) ->
                                             let w_app =
                                               let uu____81729 =
                                                 let uu____81734 =
                                                   FStar_List.map
                                                     (fun uu____81745  ->
                                                        match uu____81745
                                                        with
                                                        | (z,uu____81753) ->
                                                            let uu____81758 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____81758) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____81734
                                                  in
                                               uu____81729
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____81762 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____81762
                                               then
                                                 let uu____81767 =
                                                   let uu____81771 =
                                                     flex_t_to_string lhs  in
                                                   let uu____81773 =
                                                     let uu____81777 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____81779 =
                                                       let uu____81783 =
                                                         term_to_string w  in
                                                       let uu____81785 =
                                                         let uu____81789 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____81798 =
                                                           let uu____81802 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____81811 =
                                                             let uu____81815
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____81815]
                                                              in
                                                           uu____81802 ::
                                                             uu____81811
                                                            in
                                                         uu____81789 ::
                                                           uu____81798
                                                          in
                                                       uu____81783 ::
                                                         uu____81785
                                                        in
                                                     uu____81777 ::
                                                       uu____81779
                                                      in
                                                   uu____81771 :: uu____81773
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____81767
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____81832 =
                                                     let uu____81837 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____81837)  in
                                                   TERM uu____81832  in
                                                 let uu____81838 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____81838
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____81846 =
                                                        let uu____81851 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____81851)
                                                         in
                                                      TERM uu____81846  in
                                                    [s1; s2])
                                                  in
                                               let uu____81852 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____81852))))))
                   | uu____81853 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____81924 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____81924
            then
              let uu____81929 = FStar_Syntax_Print.term_to_string t1  in
              let uu____81931 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____81933 = FStar_Syntax_Print.term_to_string t2  in
              let uu____81935 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____81929 uu____81931 uu____81933 uu____81935
            else ());
           (let uu____81946 = FStar_Syntax_Util.head_and_args t1  in
            match uu____81946 with
            | (head1,args1) ->
                let uu____81989 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____81989 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____82059 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____82059 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____82089 =
                         let uu____82091 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____82093 = args_to_string args1  in
                         let uu____82097 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____82099 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____82091 uu____82093 uu____82097 uu____82099
                          in
                       giveup env1 uu____82089 orig
                     else
                       (let uu____82106 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____82115 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____82115 = FStar_Syntax_Util.Equal)
                           in
                        if uu____82106
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_82119 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_82119.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_82119.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_82119.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_82119.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_82119.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_82119.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_82119.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_82119.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____82129 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____82129
                                    else solve env1 wl2))
                        else
                          (let uu____82134 = base_and_refinement env1 t1  in
                           match uu____82134 with
                           | (base1,refinement1) ->
                               let uu____82159 = base_and_refinement env1 t2
                                  in
                               (match uu____82159 with
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
                                           let uu____82324 =
                                             FStar_List.fold_right
                                               (fun uu____82364  ->
                                                  fun uu____82365  ->
                                                    match (uu____82364,
                                                            uu____82365)
                                                    with
                                                    | (((a1,uu____82417),
                                                        (a2,uu____82419)),
                                                       (probs,wl3)) ->
                                                        let uu____82468 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____82468
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____82324 with
                                           | (subprobs,wl3) ->
                                               ((let uu____82511 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82511
                                                 then
                                                   let uu____82516 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____82516
                                                 else ());
                                                (let uu____82522 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____82522
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
                                                    (let uu____82549 =
                                                       mk_sub_probs wl3  in
                                                     match uu____82549 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____82565 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____82565
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____82573 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____82573))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____82597 =
                                                    mk_sub_probs wl3  in
                                                  match uu____82597 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____82611 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____82611)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____82637 =
                                           match uu____82637 with
                                           | (prob,reason) ->
                                               ((let uu____82648 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82648
                                                 then
                                                   let uu____82653 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____82655 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____82653 uu____82655
                                                     reason
                                                 else ());
                                                (let uu____82660 =
                                                   let uu____82669 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____82672 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____82669, uu____82672)
                                                    in
                                                 match uu____82660 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____82685 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____82685 with
                                                      | (head1',uu____82703)
                                                          ->
                                                          let uu____82728 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____82728
                                                           with
                                                           | (head2',uu____82746)
                                                               ->
                                                               let uu____82771
                                                                 =
                                                                 let uu____82776
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____82777
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____82776,
                                                                   uu____82777)
                                                                  in
                                                               (match uu____82771
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____82779
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82779
                                                                    then
                                                                    let uu____82784
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____82786
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____82788
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____82790
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____82784
                                                                    uu____82786
                                                                    uu____82788
                                                                    uu____82790
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____82795
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_82803
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_82803.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_82803.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_82803.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_82803.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_82803.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_82803.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_82803.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_82803.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____82805
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82805
                                                                    then
                                                                    let uu____82810
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____82810
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____82815 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____82827 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____82827 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____82835 =
                                             let uu____82836 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____82836.FStar_Syntax_Syntax.n
                                              in
                                           match uu____82835 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____82841 -> false  in
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
                                          | uu____82844 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____82847 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_82883 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_82883.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_82883.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_82883.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_82883.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_82883.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_82883.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_82883.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_82883.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____82959 = destruct_flex_t scrutinee wl1  in
             match uu____82959 with
             | ((_t,uv,_args),wl2) ->
                 let uu____82970 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____82970 with
                  | (xs,pat_term,uu____82986,uu____82987) ->
                      let uu____82992 =
                        FStar_List.fold_left
                          (fun uu____83015  ->
                             fun x  ->
                               match uu____83015 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____83036 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____83036 with
                                    | (uu____83055,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____82992 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____83076 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____83076 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_83093 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_83093.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_83093.umax_heuristic_ok);
                                    tcenv = (uu___3212_83093.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____83105 = solve env1 wl'  in
                                (match uu____83105 with
                                 | Success (uu____83108,imps) ->
                                     let wl'1 =
                                       let uu___3220_83111 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_83111.wl_deferred);
                                         ctr = (uu___3220_83111.ctr);
                                         defer_ok =
                                           (uu___3220_83111.defer_ok);
                                         smt_ok = (uu___3220_83111.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_83111.umax_heuristic_ok);
                                         tcenv = (uu___3220_83111.tcenv);
                                         wl_implicits =
                                           (uu___3220_83111.wl_implicits)
                                       }  in
                                     let uu____83112 = solve env1 wl'1  in
                                     (match uu____83112 with
                                      | Success (uu____83115,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_83119 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_83119.attempting);
                                                 wl_deferred =
                                                   (uu___3228_83119.wl_deferred);
                                                 ctr = (uu___3228_83119.ctr);
                                                 defer_ok =
                                                   (uu___3228_83119.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_83119.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_83119.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_83119.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____83120 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____83127 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____83150 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____83150
                 then
                   let uu____83155 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____83157 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____83155 uu____83157
                 else ());
                (let uu____83162 =
                   let uu____83183 =
                     let uu____83192 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____83192)  in
                   let uu____83199 =
                     let uu____83208 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____83208)  in
                   (uu____83183, uu____83199)  in
                 match uu____83162 with
                 | ((uu____83238,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____83241;
                                   FStar_Syntax_Syntax.vars = uu____83242;_}),
                    (s,t)) ->
                     let uu____83313 =
                       let uu____83315 = is_flex scrutinee  in
                       Prims.op_Negation uu____83315  in
                     if uu____83313
                     then
                       ((let uu____83326 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____83326
                         then
                           let uu____83331 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____83331
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____83350 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83350
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____83365 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83365
                           then
                             let uu____83370 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____83372 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____83370 uu____83372
                           else ());
                          (let pat_discriminates uu___613_83397 =
                             match uu___613_83397 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____83413;
                                  FStar_Syntax_Syntax.p = uu____83414;_},FStar_Pervasives_Native.None
                                ,uu____83415) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____83429;
                                  FStar_Syntax_Syntax.p = uu____83430;_},FStar_Pervasives_Native.None
                                ,uu____83431) -> true
                             | uu____83458 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____83561 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____83561 with
                                       | (uu____83563,uu____83564,t') ->
                                           let uu____83582 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____83582 with
                                            | (FullMatch ,uu____83594) ->
                                                true
                                            | (HeadMatch
                                               uu____83608,uu____83609) ->
                                                true
                                            | uu____83624 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____83661 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____83661
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____83672 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____83672 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____83760,uu____83761) ->
                                       branches1
                                   | uu____83906 -> branches  in
                                 let uu____83961 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____83970 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____83970 with
                                        | (p,uu____83974,uu____83975) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _84004  -> FStar_Util.Inr _84004)
                                   uu____83961))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84034 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84034 with
                                | (p,uu____84043,e) ->
                                    ((let uu____84062 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84062
                                      then
                                        let uu____84067 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84069 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84067 uu____84069
                                      else ());
                                     (let uu____84074 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84089  -> FStar_Util.Inr _84089)
                                        uu____84074)))))
                 | ((s,t),(uu____84092,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____84095;
                                         FStar_Syntax_Syntax.vars =
                                           uu____84096;_}))
                     ->
                     let uu____84165 =
                       let uu____84167 = is_flex scrutinee  in
                       Prims.op_Negation uu____84167  in
                     if uu____84165
                     then
                       ((let uu____84178 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____84178
                         then
                           let uu____84183 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____84183
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____84202 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84202
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____84217 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84217
                           then
                             let uu____84222 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____84224 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____84222 uu____84224
                           else ());
                          (let pat_discriminates uu___613_84249 =
                             match uu___613_84249 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____84265;
                                  FStar_Syntax_Syntax.p = uu____84266;_},FStar_Pervasives_Native.None
                                ,uu____84267) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____84281;
                                  FStar_Syntax_Syntax.p = uu____84282;_},FStar_Pervasives_Native.None
                                ,uu____84283) -> true
                             | uu____84310 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____84413 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____84413 with
                                       | (uu____84415,uu____84416,t') ->
                                           let uu____84434 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____84434 with
                                            | (FullMatch ,uu____84446) ->
                                                true
                                            | (HeadMatch
                                               uu____84460,uu____84461) ->
                                                true
                                            | uu____84476 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____84513 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____84513
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____84524 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____84524 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____84612,uu____84613) ->
                                       branches1
                                   | uu____84758 -> branches  in
                                 let uu____84813 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____84822 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____84822 with
                                        | (p,uu____84826,uu____84827) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _84856  -> FStar_Util.Inr _84856)
                                   uu____84813))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84886 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84886 with
                                | (p,uu____84895,e) ->
                                    ((let uu____84914 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84914
                                      then
                                        let uu____84919 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84921 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84919 uu____84921
                                      else ());
                                     (let uu____84926 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84941  -> FStar_Util.Inr _84941)
                                        uu____84926)))))
                 | uu____84942 ->
                     ((let uu____84964 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____84964
                       then
                         let uu____84969 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____84971 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____84969 uu____84971
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____85017 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____85017
            then
              let uu____85022 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____85024 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____85026 = FStar_Syntax_Print.term_to_string t1  in
              let uu____85028 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____85022 uu____85024 uu____85026 uu____85028
            else ());
           (let uu____85033 = head_matches_delta env1 wl1 t1 t2  in
            match uu____85033 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____85064,uu____85065) ->
                     let rec may_relate head3 =
                       let uu____85093 =
                         let uu____85094 = FStar_Syntax_Subst.compress head3
                            in
                         uu____85094.FStar_Syntax_Syntax.n  in
                       match uu____85093 with
                       | FStar_Syntax_Syntax.Tm_name uu____85098 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____85100 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____85125 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____85125 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____85127 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____85130
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____85131 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____85134,uu____85135) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____85177) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____85183) ->
                           may_relate t
                       | uu____85188 -> false  in
                     let uu____85190 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____85190 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____85211 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____85211
                          then
                            let uu____85214 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____85214 with
                             | (guard,wl2) ->
                                 let uu____85221 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____85221)
                          else
                            (let uu____85224 =
                               let uu____85226 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____85228 =
                                 let uu____85230 =
                                   let uu____85234 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____85234
                                     (fun x  ->
                                        let uu____85241 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85241)
                                    in
                                 FStar_Util.dflt "" uu____85230  in
                               let uu____85246 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____85248 =
                                 let uu____85250 =
                                   let uu____85254 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____85254
                                     (fun x  ->
                                        let uu____85261 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85261)
                                    in
                                 FStar_Util.dflt "" uu____85250  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____85226 uu____85228 uu____85246
                                 uu____85248
                                in
                             giveup env1 uu____85224 orig))
                 | (HeadMatch (true ),uu____85267) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____85282 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____85282 with
                        | (guard,wl2) ->
                            let uu____85289 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____85289)
                     else
                       (let uu____85292 =
                          let uu____85294 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____85296 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____85294 uu____85296
                           in
                        giveup env1 uu____85292 orig)
                 | (uu____85299,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_85313 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_85313.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_85313.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_85313.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_85313.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_85313.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_85313.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_85313.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_85313.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____85340 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____85340
          then
            let uu____85343 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____85343
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____85349 =
                let uu____85352 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85352  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____85349 t1);
             (let uu____85371 =
                let uu____85374 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85374  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____85371 t2);
             (let uu____85393 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____85393
              then
                let uu____85397 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____85399 =
                  let uu____85401 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____85403 =
                    let uu____85405 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____85405  in
                  Prims.op_Hat uu____85401 uu____85403  in
                let uu____85408 =
                  let uu____85410 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____85412 =
                    let uu____85414 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____85414  in
                  Prims.op_Hat uu____85410 uu____85412  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____85397 uu____85399 uu____85408
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____85421,uu____85422) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____85446,FStar_Syntax_Syntax.Tm_delayed uu____85447) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____85471,uu____85472) ->
                  let uu____85499 =
                    let uu___3432_85500 = problem  in
                    let uu____85501 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_85500.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85501;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_85500.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_85500.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_85500.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_85500.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_85500.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_85500.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_85500.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_85500.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85499 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____85502,uu____85503) ->
                  let uu____85510 =
                    let uu___3438_85511 = problem  in
                    let uu____85512 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_85511.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85512;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_85511.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_85511.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_85511.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_85511.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_85511.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_85511.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_85511.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_85511.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85510 wl
              | (uu____85513,FStar_Syntax_Syntax.Tm_ascribed uu____85514) ->
                  let uu____85541 =
                    let uu___3444_85542 = problem  in
                    let uu____85543 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_85542.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_85542.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_85542.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85543;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_85542.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_85542.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_85542.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_85542.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_85542.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_85542.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85541 wl
              | (uu____85544,FStar_Syntax_Syntax.Tm_meta uu____85545) ->
                  let uu____85552 =
                    let uu___3450_85553 = problem  in
                    let uu____85554 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_85553.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_85553.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_85553.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85554;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_85553.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_85553.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_85553.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_85553.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_85553.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_85553.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85552 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____85556),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____85558)) ->
                  let uu____85567 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____85567
              | (FStar_Syntax_Syntax.Tm_bvar uu____85568,uu____85569) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____85571,FStar_Syntax_Syntax.Tm_bvar uu____85572) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_85642 =
                    match uu___614_85642 with
                    | [] -> c
                    | bs ->
                        let uu____85670 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____85670
                     in
                  let uu____85681 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____85681 with
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
                                    let uu____85830 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____85830
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
                  let mk_t t l uu___615_85919 =
                    match uu___615_85919 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____85961 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____85961 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____86106 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____86107 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____86106
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____86107 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____86109,uu____86110) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86141 -> true
                    | uu____86161 -> false  in
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
                      (let uu____86221 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86229 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86229.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86229.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86229.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86229.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86229.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86229.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86229.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86229.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86229.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86229.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86229.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86229.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86229.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86229.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86229.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86229.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86229.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86229.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86229.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86229.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86229.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86229.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86229.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86229.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86229.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86229.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86229.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86229.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86229.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86229.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86229.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86229.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86229.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86229.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86229.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86229.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86229.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86229.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86229.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86229.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86221 with
                       | (uu____86234,ty,uu____86236) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86245 =
                                 let uu____86246 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86246.FStar_Syntax_Syntax.n  in
                               match uu____86245 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86249 ->
                                   let uu____86256 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86256
                               | uu____86257 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86260 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86260
                             then
                               let uu____86265 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86267 =
                                 let uu____86269 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86269
                                  in
                               let uu____86270 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86265 uu____86267 uu____86270
                             else ());
                            r1))
                     in
                  let uu____86275 =
                    let uu____86292 = maybe_eta t1  in
                    let uu____86299 = maybe_eta t2  in
                    (uu____86292, uu____86299)  in
                  (match uu____86275 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86341 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86341.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86341.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86341.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86341.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86341.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86341.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86341.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86341.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86362 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86362
                       then
                         let uu____86365 = destruct_flex_t not_abs wl  in
                         (match uu____86365 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86382 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86382.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86382.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86382.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86382.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86382.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86382.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86382.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86382.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86406 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86406
                       then
                         let uu____86409 = destruct_flex_t not_abs wl  in
                         (match uu____86409 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86426 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86426.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86426.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86426.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86426.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86426.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86426.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86426.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86426.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86430 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____86448,FStar_Syntax_Syntax.Tm_abs uu____86449) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86480 -> true
                    | uu____86500 -> false  in
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
                      (let uu____86560 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86568 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86568.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86568.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86568.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86568.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86568.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86568.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86568.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86568.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86568.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86568.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86568.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86568.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86568.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86568.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86568.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86568.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86568.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86568.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86568.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86568.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86568.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86568.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86568.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86568.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86568.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86568.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86568.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86568.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86568.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86568.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86568.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86568.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86568.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86568.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86568.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86568.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86568.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86568.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86568.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86568.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86560 with
                       | (uu____86573,ty,uu____86575) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86584 =
                                 let uu____86585 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86585.FStar_Syntax_Syntax.n  in
                               match uu____86584 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86588 ->
                                   let uu____86595 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86595
                               | uu____86596 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86599 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86599
                             then
                               let uu____86604 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86606 =
                                 let uu____86608 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86608
                                  in
                               let uu____86609 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86604 uu____86606 uu____86609
                             else ());
                            r1))
                     in
                  let uu____86614 =
                    let uu____86631 = maybe_eta t1  in
                    let uu____86638 = maybe_eta t2  in
                    (uu____86631, uu____86638)  in
                  (match uu____86614 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86680 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86680.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86680.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86680.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86680.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86680.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86680.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86680.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86680.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86701 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86701
                       then
                         let uu____86704 = destruct_flex_t not_abs wl  in
                         (match uu____86704 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86721 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86721.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86721.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86721.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86721.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86721.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86721.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86721.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86721.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86745 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86745
                       then
                         let uu____86748 = destruct_flex_t not_abs wl  in
                         (match uu____86748 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86765 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86765.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86765.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86765.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86765.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86765.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86765.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86765.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86765.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86769 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____86799 =
                    let uu____86804 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____86804 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_86832 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86832.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86832.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86834 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86834.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86834.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____86835,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_86850 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86850.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86850.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86852 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86852.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86852.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____86853 -> (x1, x2)  in
                  (match uu____86799 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____86872 = as_refinement false env t11  in
                       (match uu____86872 with
                        | (x12,phi11) ->
                            let uu____86880 = as_refinement false env t21  in
                            (match uu____86880 with
                             | (x22,phi21) ->
                                 ((let uu____86889 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____86889
                                   then
                                     ((let uu____86894 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____86896 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86898 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____86894
                                         uu____86896 uu____86898);
                                      (let uu____86901 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____86903 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86905 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____86901
                                         uu____86903 uu____86905))
                                   else ());
                                  (let uu____86910 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____86910 with
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
                                         let uu____86981 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____86981
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____86993 =
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
                                         (let uu____87006 =
                                            let uu____87009 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____87009
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____87006
                                            (p_guard base_prob));
                                         (let uu____87028 =
                                            let uu____87031 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____87031
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____87028
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____87050 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____87050)
                                          in
                                       let has_uvars =
                                         (let uu____87055 =
                                            let uu____87057 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____87057
                                             in
                                          Prims.op_Negation uu____87055) ||
                                           (let uu____87061 =
                                              let uu____87063 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____87063
                                               in
                                            Prims.op_Negation uu____87061)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____87067 =
                                           let uu____87072 =
                                             let uu____87081 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____87081]  in
                                           mk_t_problem wl1 uu____87072 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____87067 with
                                          | (ref_prob,wl2) ->
                                              let uu____87103 =
                                                solve env1
                                                  (let uu___3657_87105 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_87105.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_87105.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_87105.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_87105.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_87105.wl_implicits)
                                                   })
                                                 in
                                              (match uu____87103 with
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
                                               | Success uu____87122 ->
                                                   let guard =
                                                     let uu____87130 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____87130
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_87139 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_87139.attempting);
                                                       wl_deferred =
                                                         (uu___3668_87139.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_87139.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_87139.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_87139.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_87139.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_87139.wl_implicits)
                                                     }  in
                                                   let uu____87141 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____87141))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87144,FStar_Syntax_Syntax.Tm_uvar uu____87145) ->
                  let uu____87170 = destruct_flex_t t1 wl  in
                  (match uu____87170 with
                   | (f1,wl1) ->
                       let uu____87177 = destruct_flex_t t2 wl1  in
                       (match uu____87177 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87184;
                    FStar_Syntax_Syntax.pos = uu____87185;
                    FStar_Syntax_Syntax.vars = uu____87186;_},uu____87187),FStar_Syntax_Syntax.Tm_uvar
                 uu____87188) ->
                  let uu____87237 = destruct_flex_t t1 wl  in
                  (match uu____87237 with
                   | (f1,wl1) ->
                       let uu____87244 = destruct_flex_t t2 wl1  in
                       (match uu____87244 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87251,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87252;
                    FStar_Syntax_Syntax.pos = uu____87253;
                    FStar_Syntax_Syntax.vars = uu____87254;_},uu____87255))
                  ->
                  let uu____87304 = destruct_flex_t t1 wl  in
                  (match uu____87304 with
                   | (f1,wl1) ->
                       let uu____87311 = destruct_flex_t t2 wl1  in
                       (match uu____87311 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87318;
                    FStar_Syntax_Syntax.pos = uu____87319;
                    FStar_Syntax_Syntax.vars = uu____87320;_},uu____87321),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87322;
                    FStar_Syntax_Syntax.pos = uu____87323;
                    FStar_Syntax_Syntax.vars = uu____87324;_},uu____87325))
                  ->
                  let uu____87398 = destruct_flex_t t1 wl  in
                  (match uu____87398 with
                   | (f1,wl1) ->
                       let uu____87405 = destruct_flex_t t2 wl1  in
                       (match uu____87405 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____87412,uu____87413) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87426 = destruct_flex_t t1 wl  in
                  (match uu____87426 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87433;
                    FStar_Syntax_Syntax.pos = uu____87434;
                    FStar_Syntax_Syntax.vars = uu____87435;_},uu____87436),uu____87437)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87474 = destruct_flex_t t1 wl  in
                  (match uu____87474 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____87481,FStar_Syntax_Syntax.Tm_uvar uu____87482) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____87495,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87496;
                    FStar_Syntax_Syntax.pos = uu____87497;
                    FStar_Syntax_Syntax.vars = uu____87498;_},uu____87499))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87536,FStar_Syntax_Syntax.Tm_arrow uu____87537) ->
                  solve_t' env
                    (let uu___3768_87565 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87565.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87565.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87565.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87565.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87565.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87565.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87565.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87565.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87565.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87566;
                    FStar_Syntax_Syntax.pos = uu____87567;
                    FStar_Syntax_Syntax.vars = uu____87568;_},uu____87569),FStar_Syntax_Syntax.Tm_arrow
                 uu____87570) ->
                  solve_t' env
                    (let uu___3768_87622 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87622.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87622.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87622.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87622.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87622.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87622.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87622.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87622.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87622.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87623,FStar_Syntax_Syntax.Tm_uvar uu____87624) ->
                  let uu____87637 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87637
              | (uu____87638,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87639;
                    FStar_Syntax_Syntax.pos = uu____87640;
                    FStar_Syntax_Syntax.vars = uu____87641;_},uu____87642))
                  ->
                  let uu____87679 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87679
              | (FStar_Syntax_Syntax.Tm_uvar uu____87680,uu____87681) ->
                  let uu____87694 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87694
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87695;
                    FStar_Syntax_Syntax.pos = uu____87696;
                    FStar_Syntax_Syntax.vars = uu____87697;_},uu____87698),uu____87699)
                  ->
                  let uu____87736 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87736
              | (FStar_Syntax_Syntax.Tm_refine uu____87737,uu____87738) ->
                  let t21 =
                    let uu____87746 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____87746  in
                  solve_t env
                    (let uu___3803_87772 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_87772.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_87772.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_87772.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_87772.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_87772.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_87772.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_87772.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_87772.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_87772.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87773,FStar_Syntax_Syntax.Tm_refine uu____87774) ->
                  let t11 =
                    let uu____87782 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____87782  in
                  solve_t env
                    (let uu___3810_87808 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_87808.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_87808.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_87808.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_87808.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_87808.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_87808.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_87808.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_87808.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_87808.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____87890 =
                    let uu____87891 = guard_of_prob env wl problem t1 t2  in
                    match uu____87891 with
                    | (guard,wl1) ->
                        let uu____87898 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____87898
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____88117 = br1  in
                        (match uu____88117 with
                         | (p1,w1,uu____88146) ->
                             let uu____88163 = br2  in
                             (match uu____88163 with
                              | (p2,w2,uu____88186) ->
                                  let uu____88191 =
                                    let uu____88193 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____88193  in
                                  if uu____88191
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____88220 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____88220 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____88257 = br2  in
                                         (match uu____88257 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____88290 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____88290
                                                 in
                                              let uu____88295 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____88326,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____88347) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____88406 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____88406 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____88295
                                                (fun uu____88478  ->
                                                   match uu____88478 with
                                                   | (wprobs,wl2) ->
                                                       let uu____88515 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____88515
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____88536
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____88536
                                                              then
                                                                let uu____88541
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____88543
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____88541
                                                                  uu____88543
                                                              else ());
                                                             (let uu____88549
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____88549
                                                                (fun
                                                                   uu____88585
                                                                    ->
                                                                   match uu____88585
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
                    | uu____88714 -> FStar_Pervasives_Native.None  in
                  let uu____88755 = solve_branches wl brs1 brs2  in
                  (match uu____88755 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____88806 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____88806 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____88840 =
                                FStar_List.map
                                  (fun uu____88852  ->
                                     match uu____88852 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____88840  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____88861 =
                              let uu____88862 =
                                let uu____88863 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____88863
                                  (let uu___3909_88871 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_88871.attempting);
                                     wl_deferred =
                                       (uu___3909_88871.wl_deferred);
                                     ctr = (uu___3909_88871.ctr);
                                     defer_ok = (uu___3909_88871.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_88871.umax_heuristic_ok);
                                     tcenv = (uu___3909_88871.tcenv);
                                     wl_implicits =
                                       (uu___3909_88871.wl_implicits)
                                   })
                                 in
                              solve env uu____88862  in
                            (match uu____88861 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____88876 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____88883,uu____88884) ->
                  let head1 =
                    let uu____88908 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____88908
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____88954 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____88954
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89000 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89000
                    then
                      let uu____89004 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89006 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89008 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89004 uu____89006 uu____89008
                    else ());
                   (let no_free_uvars t =
                      (let uu____89022 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89022) &&
                        (let uu____89026 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89026)
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
                      let uu____89043 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89043 = FStar_Syntax_Util.Equal  in
                    let uu____89044 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89044
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89048 = equal t1 t2  in
                         (if uu____89048
                          then
                            let uu____89051 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89051
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89056 =
                            let uu____89063 = equal t1 t2  in
                            if uu____89063
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89076 = mk_eq2 wl env orig t1 t2  in
                               match uu____89076 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89056 with
                          | (guard,wl1) ->
                              let uu____89097 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89097))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____89100,uu____89101) ->
                  let head1 =
                    let uu____89109 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89109
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89155 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89155
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89201 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89201
                    then
                      let uu____89205 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89207 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89209 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89205 uu____89207 uu____89209
                    else ());
                   (let no_free_uvars t =
                      (let uu____89223 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89223) &&
                        (let uu____89227 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89227)
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
                      let uu____89244 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89244 = FStar_Syntax_Util.Equal  in
                    let uu____89245 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89245
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89249 = equal t1 t2  in
                         (if uu____89249
                          then
                            let uu____89252 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89252
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89257 =
                            let uu____89264 = equal t1 t2  in
                            if uu____89264
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89277 = mk_eq2 wl env orig t1 t2  in
                               match uu____89277 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89257 with
                          | (guard,wl1) ->
                              let uu____89298 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89298))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____89301,uu____89302) ->
                  let head1 =
                    let uu____89304 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89304
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89350 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89350
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89396 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89396
                    then
                      let uu____89400 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89402 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89404 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89400 uu____89402 uu____89404
                    else ());
                   (let no_free_uvars t =
                      (let uu____89418 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89418) &&
                        (let uu____89422 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89422)
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
                      let uu____89439 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89439 = FStar_Syntax_Util.Equal  in
                    let uu____89440 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89440
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89444 = equal t1 t2  in
                         (if uu____89444
                          then
                            let uu____89447 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89447
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89452 =
                            let uu____89459 = equal t1 t2  in
                            if uu____89459
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89472 = mk_eq2 wl env orig t1 t2  in
                               match uu____89472 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89452 with
                          | (guard,wl1) ->
                              let uu____89493 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89493))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____89496,uu____89497) ->
                  let head1 =
                    let uu____89499 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89499
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89545 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89545
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89591 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89591
                    then
                      let uu____89595 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89597 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89599 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89595 uu____89597 uu____89599
                    else ());
                   (let no_free_uvars t =
                      (let uu____89613 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89613) &&
                        (let uu____89617 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89617)
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
                      let uu____89634 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89634 = FStar_Syntax_Util.Equal  in
                    let uu____89635 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89635
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89639 = equal t1 t2  in
                         (if uu____89639
                          then
                            let uu____89642 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89642
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89647 =
                            let uu____89654 = equal t1 t2  in
                            if uu____89654
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89667 = mk_eq2 wl env orig t1 t2  in
                               match uu____89667 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89647 with
                          | (guard,wl1) ->
                              let uu____89688 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89688))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____89691,uu____89692) ->
                  let head1 =
                    let uu____89694 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89694
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89740 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89740
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89786 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89786
                    then
                      let uu____89790 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89792 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89794 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89790 uu____89792 uu____89794
                    else ());
                   (let no_free_uvars t =
                      (let uu____89808 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89808) &&
                        (let uu____89812 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89812)
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
                      let uu____89829 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89829 = FStar_Syntax_Util.Equal  in
                    let uu____89830 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89830
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89834 = equal t1 t2  in
                         (if uu____89834
                          then
                            let uu____89837 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89837
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89842 =
                            let uu____89849 = equal t1 t2  in
                            if uu____89849
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89862 = mk_eq2 wl env orig t1 t2  in
                               match uu____89862 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89842 with
                          | (guard,wl1) ->
                              let uu____89883 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89883))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____89886,uu____89887) ->
                  let head1 =
                    let uu____89905 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89905
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89951 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89951
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89997 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89997
                    then
                      let uu____90001 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90003 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90005 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90001 uu____90003 uu____90005
                    else ());
                   (let no_free_uvars t =
                      (let uu____90019 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90019) &&
                        (let uu____90023 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90023)
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
                      let uu____90040 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90040 = FStar_Syntax_Util.Equal  in
                    let uu____90041 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90041
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90045 = equal t1 t2  in
                         (if uu____90045
                          then
                            let uu____90048 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90048
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90053 =
                            let uu____90060 = equal t1 t2  in
                            if uu____90060
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90073 = mk_eq2 wl env orig t1 t2  in
                               match uu____90073 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90053 with
                          | (guard,wl1) ->
                              let uu____90094 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90094))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90097,FStar_Syntax_Syntax.Tm_match uu____90098) ->
                  let head1 =
                    let uu____90122 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90122
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90168 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90168
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90214 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90214
                    then
                      let uu____90218 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90220 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90222 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90218 uu____90220 uu____90222
                    else ());
                   (let no_free_uvars t =
                      (let uu____90236 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90236) &&
                        (let uu____90240 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90240)
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
                      let uu____90257 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90257 = FStar_Syntax_Util.Equal  in
                    let uu____90258 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90258
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90262 = equal t1 t2  in
                         (if uu____90262
                          then
                            let uu____90265 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90265
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90270 =
                            let uu____90277 = equal t1 t2  in
                            if uu____90277
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90290 = mk_eq2 wl env orig t1 t2  in
                               match uu____90290 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90270 with
                          | (guard,wl1) ->
                              let uu____90311 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90311))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90314,FStar_Syntax_Syntax.Tm_uinst uu____90315) ->
                  let head1 =
                    let uu____90323 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90323
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90363 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90363
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90403 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90403
                    then
                      let uu____90407 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90409 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90411 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90407 uu____90409 uu____90411
                    else ());
                   (let no_free_uvars t =
                      (let uu____90425 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90425) &&
                        (let uu____90429 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90429)
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
                      let uu____90446 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90446 = FStar_Syntax_Util.Equal  in
                    let uu____90447 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90447
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90451 = equal t1 t2  in
                         (if uu____90451
                          then
                            let uu____90454 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90454
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90459 =
                            let uu____90466 = equal t1 t2  in
                            if uu____90466
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90479 = mk_eq2 wl env orig t1 t2  in
                               match uu____90479 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90459 with
                          | (guard,wl1) ->
                              let uu____90500 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90500))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90503,FStar_Syntax_Syntax.Tm_name uu____90504) ->
                  let head1 =
                    let uu____90506 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90506
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90546 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90546
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90586 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90586
                    then
                      let uu____90590 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90592 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90594 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90590 uu____90592 uu____90594
                    else ());
                   (let no_free_uvars t =
                      (let uu____90608 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90608) &&
                        (let uu____90612 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90612)
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
                      let uu____90629 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90629 = FStar_Syntax_Util.Equal  in
                    let uu____90630 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90630
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90634 = equal t1 t2  in
                         (if uu____90634
                          then
                            let uu____90637 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90637
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90642 =
                            let uu____90649 = equal t1 t2  in
                            if uu____90649
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90662 = mk_eq2 wl env orig t1 t2  in
                               match uu____90662 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90642 with
                          | (guard,wl1) ->
                              let uu____90683 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90683))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90686,FStar_Syntax_Syntax.Tm_constant uu____90687) ->
                  let head1 =
                    let uu____90689 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90689
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90729 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90729
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90769 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90769
                    then
                      let uu____90773 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90775 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90777 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90773 uu____90775 uu____90777
                    else ());
                   (let no_free_uvars t =
                      (let uu____90791 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90791) &&
                        (let uu____90795 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90795)
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
                      let uu____90812 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90812 = FStar_Syntax_Util.Equal  in
                    let uu____90813 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90813
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90817 = equal t1 t2  in
                         (if uu____90817
                          then
                            let uu____90820 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90820
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90825 =
                            let uu____90832 = equal t1 t2  in
                            if uu____90832
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90845 = mk_eq2 wl env orig t1 t2  in
                               match uu____90845 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90825 with
                          | (guard,wl1) ->
                              let uu____90866 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90866))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90869,FStar_Syntax_Syntax.Tm_fvar uu____90870) ->
                  let head1 =
                    let uu____90872 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90872
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90912 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90912
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90952 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90952
                    then
                      let uu____90956 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90958 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90960 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90956 uu____90958 uu____90960
                    else ());
                   (let no_free_uvars t =
                      (let uu____90974 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90974) &&
                        (let uu____90978 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90978)
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
                      let uu____90995 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90995 = FStar_Syntax_Util.Equal  in
                    let uu____90996 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90996
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____91000 = equal t1 t2  in
                         (if uu____91000
                          then
                            let uu____91003 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____91003
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____91008 =
                            let uu____91015 = equal t1 t2  in
                            if uu____91015
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91028 = mk_eq2 wl env orig t1 t2  in
                               match uu____91028 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____91008 with
                          | (guard,wl1) ->
                              let uu____91049 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91049))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____91052,FStar_Syntax_Syntax.Tm_app uu____91053) ->
                  let head1 =
                    let uu____91071 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____91071
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____91111 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____91111
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____91151 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____91151
                    then
                      let uu____91155 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____91157 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____91159 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____91155 uu____91157 uu____91159
                    else ());
                   (let no_free_uvars t =
                      (let uu____91173 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____91173) &&
                        (let uu____91177 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____91177)
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
                      let uu____91194 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____91194 = FStar_Syntax_Util.Equal  in
                    let uu____91195 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____91195
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____91199 = equal t1 t2  in
                         (if uu____91199
                          then
                            let uu____91202 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____91202
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____91207 =
                            let uu____91214 = equal t1 t2  in
                            if uu____91214
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91227 = mk_eq2 wl env orig t1 t2  in
                               match uu____91227 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____91207 with
                          | (guard,wl1) ->
                              let uu____91248 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91248))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____91251,FStar_Syntax_Syntax.Tm_let uu____91252) ->
                  let uu____91279 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____91279
                  then
                    let uu____91282 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____91282
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____91286,uu____91287) ->
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
              | (uu____91319,FStar_Syntax_Syntax.Tm_let uu____91320) ->
                  let uu____91334 =
                    let uu____91340 =
                      let uu____91342 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91344 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91346 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91348 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91342 uu____91344 uu____91346 uu____91348
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91340)
                     in
                  FStar_Errors.raise_error uu____91334
                    t1.FStar_Syntax_Syntax.pos
              | uu____91352 -> giveup env "head tag mismatch" orig))))

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
          (let uu____91416 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____91416
           then
             let uu____91421 =
               let uu____91423 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____91423  in
             let uu____91424 =
               let uu____91426 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____91426  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____91421 uu____91424
           else ());
          (let uu____91430 =
             let uu____91432 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____91432  in
           if uu____91430
           then
             let uu____91435 =
               let uu____91437 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____91439 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____91437 uu____91439
                in
             giveup env uu____91435 orig
           else
             (let uu____91444 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____91444 with
              | (ret_sub_prob,wl1) ->
                  let uu____91452 =
                    FStar_List.fold_right2
                      (fun uu____91489  ->
                         fun uu____91490  ->
                           fun uu____91491  ->
                             match (uu____91489, uu____91490, uu____91491)
                             with
                             | ((a1,uu____91535),(a2,uu____91537),(arg_sub_probs,wl2))
                                 ->
                                 let uu____91570 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____91570 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____91452 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____91600 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____91600  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____91608 = attempt sub_probs wl3  in
                       solve env uu____91608)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____91631 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____91634)::[] -> wp1
              | uu____91659 ->
                  let uu____91670 =
                    let uu____91672 =
                      let uu____91674 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____91674  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____91672
                     in
                  failwith uu____91670
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____91681 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____91681]
              | x -> x  in
            let uu____91683 =
              let uu____91694 =
                let uu____91703 =
                  let uu____91704 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____91704 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____91703  in
              [uu____91694]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____91683;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____91722 = lift_c1 ()  in solve_eq uu____91722 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_91731  ->
                       match uu___616_91731 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____91736 -> false))
                in
             let uu____91738 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____91768)::uu____91769,(wp2,uu____91771)::uu____91772)
                   -> (wp1, wp2)
               | uu____91845 ->
                   let uu____91870 =
                     let uu____91876 =
                       let uu____91878 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____91880 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____91878 uu____91880
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____91876)
                      in
                   FStar_Errors.raise_error uu____91870
                     env.FStar_TypeChecker_Env.range
                in
             match uu____91738 with
             | (wpc1,wpc2) ->
                 let uu____91890 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____91890
                 then
                   let uu____91895 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____91895 wl
                 else
                   (let uu____91899 =
                      let uu____91906 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____91906  in
                    match uu____91899 with
                    | (c2_decl,qualifiers) ->
                        let uu____91927 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____91927
                        then
                          let c1_repr =
                            let uu____91934 =
                              let uu____91935 =
                                let uu____91936 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____91936  in
                              let uu____91937 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91935 uu____91937
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91934
                             in
                          let c2_repr =
                            let uu____91939 =
                              let uu____91940 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____91941 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91940 uu____91941
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91939
                             in
                          let uu____91942 =
                            let uu____91947 =
                              let uu____91949 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____91951 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____91949 uu____91951
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____91947
                             in
                          (match uu____91942 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____91957 = attempt [prob] wl2  in
                               solve env uu____91957)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____91972 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____91972
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____91981 =
                                     let uu____91988 =
                                       let uu____91989 =
                                         let uu____92006 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____92009 =
                                           let uu____92020 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____92029 =
                                             let uu____92040 =
                                               let uu____92049 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____92049
                                                in
                                             [uu____92040]  in
                                           uu____92020 :: uu____92029  in
                                         (uu____92006, uu____92009)  in
                                       FStar_Syntax_Syntax.Tm_app uu____91989
                                        in
                                     FStar_Syntax_Syntax.mk uu____91988  in
                                   uu____91981 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____92101 =
                                    let uu____92108 =
                                      let uu____92109 =
                                        let uu____92126 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____92129 =
                                          let uu____92140 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____92149 =
                                            let uu____92160 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____92169 =
                                              let uu____92180 =
                                                let uu____92189 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____92189
                                                 in
                                              [uu____92180]  in
                                            uu____92160 :: uu____92169  in
                                          uu____92140 :: uu____92149  in
                                        (uu____92126, uu____92129)  in
                                      FStar_Syntax_Syntax.Tm_app uu____92109
                                       in
                                    FStar_Syntax_Syntax.mk uu____92108  in
                                  uu____92101 FStar_Pervasives_Native.None r)
                              in
                           (let uu____92246 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92246
                            then
                              let uu____92251 =
                                let uu____92253 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____92253
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____92251
                            else ());
                           (let uu____92257 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____92257 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____92266 =
                                    let uu____92269 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _92272  ->
                                         FStar_Pervasives_Native.Some _92272)
                                      uu____92269
                                     in
                                  solve_prob orig uu____92266 [] wl1  in
                                let uu____92273 = attempt [base_prob] wl2  in
                                solve env uu____92273))))
           in
        let uu____92274 = FStar_Util.physical_equality c1 c2  in
        if uu____92274
        then
          let uu____92277 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____92277
        else
          ((let uu____92281 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____92281
            then
              let uu____92286 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____92288 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____92286
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____92288
            else ());
           (let uu____92293 =
              let uu____92302 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____92305 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____92302, uu____92305)  in
            match uu____92293 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92323),FStar_Syntax_Syntax.Total
                    (t2,uu____92325)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____92342 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92342 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92344,FStar_Syntax_Syntax.Total uu____92345) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92364),FStar_Syntax_Syntax.Total
                    (t2,uu____92366)) ->
                     let uu____92383 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92383 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92386),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92388)) ->
                     let uu____92405 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92405 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92408),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92410)) ->
                     let uu____92427 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92427 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92429,FStar_Syntax_Syntax.Comp uu____92430) ->
                     let uu____92439 =
                       let uu___4158_92442 = problem  in
                       let uu____92445 =
                         let uu____92446 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92446
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92442.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92445;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92442.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92442.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92442.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92442.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92442.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92442.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92442.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92442.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92439 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____92447,FStar_Syntax_Syntax.Comp uu____92448) ->
                     let uu____92457 =
                       let uu___4158_92460 = problem  in
                       let uu____92463 =
                         let uu____92464 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92464
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92460.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92463;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92460.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92460.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92460.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92460.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92460.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92460.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92460.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92460.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92457 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92465,FStar_Syntax_Syntax.GTotal uu____92466) ->
                     let uu____92475 =
                       let uu___4170_92478 = problem  in
                       let uu____92481 =
                         let uu____92482 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92482
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92478.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92478.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92478.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92481;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92478.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92478.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92478.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92478.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92478.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92478.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92475 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92483,FStar_Syntax_Syntax.Total uu____92484) ->
                     let uu____92493 =
                       let uu___4170_92496 = problem  in
                       let uu____92499 =
                         let uu____92500 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92500
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92496.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92496.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92496.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92499;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92496.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92496.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92496.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92496.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92496.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92496.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92493 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92501,FStar_Syntax_Syntax.Comp uu____92502) ->
                     let uu____92503 =
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
                     if uu____92503
                     then
                       let uu____92506 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____92506 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____92513 =
                            let uu____92518 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____92518
                            then (c1_comp, c2_comp)
                            else
                              (let uu____92527 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____92528 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____92527, uu____92528))
                             in
                          match uu____92513 with
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
                           (let uu____92536 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92536
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____92544 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____92544 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____92547 =
                                  let uu____92549 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____92551 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____92549 uu____92551
                                   in
                                giveup env uu____92547 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____92562 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____92562 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____92612 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____92612 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____92637 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____92668  ->
                match uu____92668 with
                | (u1,u2) ->
                    let uu____92676 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____92678 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____92676 uu____92678))
         in
      FStar_All.pipe_right uu____92637 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____92715,[])) when
          let uu____92742 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____92742 -> "{}"
      | uu____92745 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____92772 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____92772
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____92784 =
              FStar_List.map
                (fun uu____92797  ->
                   match uu____92797 with
                   | (uu____92804,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____92784 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____92815 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____92815 imps
  
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
                  let uu____92872 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____92872
                  then
                    let uu____92880 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____92882 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____92880
                      (rel_to_string rel) uu____92882
                  else "TOP"  in
                let uu____92888 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____92888 with
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
              let uu____92948 =
                let uu____92951 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _92954  -> FStar_Pervasives_Native.Some _92954)
                  uu____92951
                 in
              FStar_Syntax_Syntax.new_bv uu____92948 t1  in
            let uu____92955 =
              let uu____92960 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____92960
               in
            match uu____92955 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____93020 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____93020
         then
           let uu____93025 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____93025
         else ());
        (let uu____93032 =
           FStar_Util.record_time (fun uu____93039  -> solve env probs)  in
         match uu____93032 with
         | (sol,ms) ->
             ((let uu____93051 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____93051
               then
                 let uu____93056 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____93056
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____93069 =
                     FStar_Util.record_time
                       (fun uu____93076  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____93069 with
                    | ((),ms1) ->
                        ((let uu____93087 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____93087
                          then
                            let uu____93092 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____93092
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____93106 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____93106
                     then
                       let uu____93113 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____93113
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
          ((let uu____93140 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____93140
            then
              let uu____93145 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____93145
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____93152 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____93152
             then
               let uu____93157 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____93157
             else ());
            (let f2 =
               let uu____93163 =
                 let uu____93164 = FStar_Syntax_Util.unmeta f1  in
                 uu____93164.FStar_Syntax_Syntax.n  in
               match uu____93163 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____93168 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_93169 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_93169.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_93169.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_93169.FStar_TypeChecker_Env.implicits)
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
            let uu____93224 =
              let uu____93225 =
                let uu____93226 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _93227  ->
                       FStar_TypeChecker_Common.NonTrivial _93227)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____93226;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____93225  in
            FStar_All.pipe_left
              (fun _93234  -> FStar_Pervasives_Native.Some _93234)
              uu____93224
  
let with_guard_no_simp :
  'Auu____93244 .
    'Auu____93244 ->
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
            let uu____93267 =
              let uu____93268 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _93269  -> FStar_TypeChecker_Common.NonTrivial _93269)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____93268;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____93267
  
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
          (let uu____93302 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____93302
           then
             let uu____93307 = FStar_Syntax_Print.term_to_string t1  in
             let uu____93309 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____93307
               uu____93309
           else ());
          (let uu____93314 =
             let uu____93319 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____93319
              in
           match uu____93314 with
           | (prob,wl) ->
               let g =
                 let uu____93327 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____93337  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____93327  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____93373 = try_teq true env t1 t2  in
        match uu____93373 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____93378 = FStar_TypeChecker_Env.get_range env  in
              let uu____93379 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____93378 uu____93379);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____93387 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____93387
              then
                let uu____93392 = FStar_Syntax_Print.term_to_string t1  in
                let uu____93394 = FStar_Syntax_Print.term_to_string t2  in
                let uu____93396 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____93392
                  uu____93394 uu____93396
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
          let uu____93422 = FStar_TypeChecker_Env.get_range env  in
          let uu____93423 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____93422 uu____93423
  
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
        (let uu____93452 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____93452
         then
           let uu____93457 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____93459 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____93457 uu____93459
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____93470 =
           let uu____93477 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____93477 "sub_comp"
            in
         match uu____93470 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____93490 =
                 FStar_Util.record_time
                   (fun uu____93502  ->
                      let uu____93503 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____93514  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____93503)
                  in
               match uu____93490 with
               | (r,ms) ->
                   ((let uu____93545 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____93545
                     then
                       let uu____93550 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____93552 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____93554 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____93550 uu____93552
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____93554
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
      fun uu____93592  ->
        match uu____93592 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____93635 =
                 let uu____93641 =
                   let uu____93643 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____93645 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____93643 uu____93645
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____93641)  in
               let uu____93649 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____93635 uu____93649)
               in
            let equiv1 v1 v' =
              let uu____93662 =
                let uu____93667 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____93668 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____93667, uu____93668)  in
              match uu____93662 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____93688 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____93719 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____93719 with
                      | FStar_Syntax_Syntax.U_unif uu____93726 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____93755  ->
                                    match uu____93755 with
                                    | (u,v') ->
                                        let uu____93764 = equiv1 v1 v'  in
                                        if uu____93764
                                        then
                                          let uu____93769 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____93769 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____93790 -> []))
               in
            let uu____93795 =
              let wl =
                let uu___4377_93799 = empty_worklist env  in
                {
                  attempting = (uu___4377_93799.attempting);
                  wl_deferred = (uu___4377_93799.wl_deferred);
                  ctr = (uu___4377_93799.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_93799.smt_ok);
                  umax_heuristic_ok = (uu___4377_93799.umax_heuristic_ok);
                  tcenv = (uu___4377_93799.tcenv);
                  wl_implicits = (uu___4377_93799.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____93818  ->
                      match uu____93818 with
                      | (lb,v1) ->
                          let uu____93825 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____93825 with
                           | USolved wl1 -> ()
                           | uu____93828 -> fail1 lb v1)))
               in
            let rec check_ineq uu____93839 =
              match uu____93839 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____93851) -> true
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
                      uu____93875,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____93877,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____93888) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____93896,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____93905 -> false)
               in
            let uu____93911 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____93928  ->
                      match uu____93928 with
                      | (u,v1) ->
                          let uu____93936 = check_ineq (u, v1)  in
                          if uu____93936
                          then true
                          else
                            ((let uu____93944 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____93944
                              then
                                let uu____93949 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____93951 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____93949
                                  uu____93951
                              else ());
                             false)))
               in
            if uu____93911
            then ()
            else
              ((let uu____93961 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____93961
                then
                  ((let uu____93967 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____93967);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____93979 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____93979))
                else ());
               (let uu____93992 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____93992))
  
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
        let fail1 uu____94066 =
          match uu____94066 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_94092 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_94092.attempting);
            wl_deferred = (uu___4454_94092.wl_deferred);
            ctr = (uu___4454_94092.ctr);
            defer_ok;
            smt_ok = (uu___4454_94092.smt_ok);
            umax_heuristic_ok = (uu___4454_94092.umax_heuristic_ok);
            tcenv = (uu___4454_94092.tcenv);
            wl_implicits = (uu___4454_94092.wl_implicits)
          }  in
        (let uu____94095 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____94095
         then
           let uu____94100 = FStar_Util.string_of_bool defer_ok  in
           let uu____94102 = wl_to_string wl  in
           let uu____94104 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____94100 uu____94102 uu____94104
         else ());
        (let g1 =
           let uu____94110 = solve_and_commit env wl fail1  in
           match uu____94110 with
           | FStar_Pervasives_Native.Some
               (uu____94117::uu____94118,uu____94119) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_94148 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_94148.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_94148.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____94149 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_94158 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_94158.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_94158.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_94158.FStar_TypeChecker_Env.implicits)
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
    let uu____94212 = FStar_ST.op_Bang last_proof_ns  in
    match uu____94212 with
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
            let uu___4493_94337 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_94337.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_94337.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_94337.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____94338 =
            let uu____94340 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____94340  in
          if uu____94338
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____94352 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____94353 =
                       let uu____94355 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____94355
                        in
                     FStar_Errors.diag uu____94352 uu____94353)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____94363 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____94364 =
                        let uu____94366 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____94366
                         in
                      FStar_Errors.diag uu____94363 uu____94364)
                   else ();
                   (let uu____94372 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____94372
                      "discharge_guard'" env vc1);
                   (let uu____94374 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____94374 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____94383 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94384 =
                                let uu____94386 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____94386
                                 in
                              FStar_Errors.diag uu____94383 uu____94384)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____94396 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94397 =
                                let uu____94399 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____94399
                                 in
                              FStar_Errors.diag uu____94396 uu____94397)
                           else ();
                           (let vcs =
                              let uu____94413 = FStar_Options.use_tactics ()
                                 in
                              if uu____94413
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____94435  ->
                                     (let uu____94437 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____94437);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____94481  ->
                                              match uu____94481 with
                                              | (env1,goal,opts) ->
                                                  let uu____94497 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____94497, opts)))))
                              else
                                (let uu____94500 =
                                   let uu____94507 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____94507)  in
                                 [uu____94500])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____94540  ->
                                    match uu____94540 with
                                    | (env1,goal,opts) ->
                                        let uu____94550 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____94550 with
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
                                                (let uu____94562 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94563 =
                                                   let uu____94565 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____94567 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____94565 uu____94567
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94562 uu____94563)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____94574 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94575 =
                                                   let uu____94577 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____94577
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94574 uu____94575)
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
      let uu____94595 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____94595 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____94604 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____94604
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____94618 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____94618 with
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
        let uu____94648 = try_teq false env t1 t2  in
        match uu____94648 with
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
            let uu____94692 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____94692 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____94705 ->
                     let uu____94718 =
                       let uu____94719 = FStar_Syntax_Subst.compress r  in
                       uu____94719.FStar_Syntax_Syntax.n  in
                     (match uu____94718 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____94724) ->
                          unresolved ctx_u'
                      | uu____94741 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____94765 = acc  in
            match uu____94765 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____94784 = hd1  in
                     (match uu____94784 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____94795 = unresolved ctx_u  in
                             if uu____94795
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____94819 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____94819
                                     then
                                       let uu____94823 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____94823
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____94832 = teq_nosmt env1 t tm
                                          in
                                       match uu____94832 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_94842 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_94842.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_94842.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_94842.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_94842.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_94842.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_94842.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_94842.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_94850 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_94850.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_94850.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_94850.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_94861 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_94861.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_94861.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_94861.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_94861.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_94861.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_94861.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_94861.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_94861.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_94861.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_94861.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_94861.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_94861.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_94861.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_94861.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_94861.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_94861.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_94861.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_94861.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_94861.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_94861.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_94861.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_94861.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_94861.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_94861.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_94861.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_94861.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_94861.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_94861.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_94861.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_94861.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_94861.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_94861.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_94861.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_94861.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_94861.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_94861.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_94861.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_94861.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_94861.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_94861.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_94861.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_94861.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_94865 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_94865.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_94865.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_94865.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_94865.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_94865.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_94865.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_94865.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_94865.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_94865.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_94865.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_94865.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_94865.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_94865.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_94865.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_94865.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_94865.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_94865.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_94865.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_94865.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_94865.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_94865.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_94865.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_94865.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_94865.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_94865.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_94865.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_94865.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_94865.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_94865.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_94865.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_94865.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_94865.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_94865.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_94865.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_94865.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_94865.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_94865.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_94865.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_94865.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_94865.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_94865.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_94865.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____94870 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____94870
                                   then
                                     let uu____94875 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____94877 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____94879 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____94881 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____94875 uu____94877 uu____94879
                                       reason uu____94881
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_94888  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____94895 =
                                             let uu____94905 =
                                               let uu____94913 =
                                                 let uu____94915 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____94917 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____94919 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____94915 uu____94917
                                                   uu____94919
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____94913, r)
                                                in
                                             [uu____94905]  in
                                           FStar_Errors.add_errors
                                             uu____94895);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_94939 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_94939.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_94939.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_94939.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____94943 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____94954  ->
                                               let uu____94955 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____94957 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____94959 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____94955 uu____94957
                                                 reason uu____94959)) env2 g2
                                         true
                                        in
                                     match uu____94943 with
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
          let uu___4640_94967 = g  in
          let uu____94968 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_94967.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_94967.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_94967.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____94968
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
        let uu____95011 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____95011 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____95012 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____95012
      | imp::uu____95014 ->
          let uu____95017 =
            let uu____95023 =
              let uu____95025 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____95027 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____95025 uu____95027 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____95023)
             in
          FStar_Errors.raise_error uu____95017
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95049 = teq_nosmt env t1 t2  in
        match uu____95049 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_95068 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_95068.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_95068.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_95068.FStar_TypeChecker_Env.implicits)
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
        (let uu____95104 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95104
         then
           let uu____95109 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95111 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____95109
             uu____95111
         else ());
        (let uu____95116 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95116 with
         | (prob,x,wl) ->
             let g =
               let uu____95135 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____95146  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95135  in
             ((let uu____95167 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____95167
               then
                 let uu____95172 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____95174 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____95176 =
                   let uu____95178 = FStar_Util.must g  in
                   guard_to_string env uu____95178  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____95172 uu____95174 uu____95176
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
        let uu____95215 = check_subtyping env t1 t2  in
        match uu____95215 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95234 =
              let uu____95235 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____95235 g  in
            FStar_Pervasives_Native.Some uu____95234
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95254 = check_subtyping env t1 t2  in
        match uu____95254 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95273 =
              let uu____95274 =
                let uu____95275 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____95275]  in
              FStar_TypeChecker_Env.close_guard env uu____95274 g  in
            FStar_Pervasives_Native.Some uu____95273
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____95313 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95313
         then
           let uu____95318 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95320 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____95318
             uu____95320
         else ());
        (let uu____95325 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95325 with
         | (prob,x,wl) ->
             let g =
               let uu____95340 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____95351  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95340  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____95375 =
                      let uu____95376 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____95376]  in
                    FStar_TypeChecker_Env.close_guard env uu____95375 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95417 = subtype_nosmt env t1 t2  in
        match uu____95417 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  