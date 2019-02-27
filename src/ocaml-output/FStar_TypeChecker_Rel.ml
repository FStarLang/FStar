open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____65058 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____65094 -> false
  
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
                    let uu____65518 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____65518;
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
                     (let uu___656_65550 = wl  in
                      {
                        attempting = (uu___656_65550.attempting);
                        wl_deferred = (uu___656_65550.wl_deferred);
                        ctr = (uu___656_65550.ctr);
                        defer_ok = (uu___656_65550.defer_ok);
                        smt_ok = (uu___656_65550.smt_ok);
                        umax_heuristic_ok =
                          (uu___656_65550.umax_heuristic_ok);
                        tcenv = (uu___656_65550.tcenv);
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
            let uu___662_65583 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___662_65583.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___662_65583.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___662_65583.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___662_65583.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___662_65583.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___662_65583.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___662_65583.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___662_65583.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___662_65583.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___662_65583.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___662_65583.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___662_65583.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___662_65583.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___662_65583.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___662_65583.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___662_65583.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___662_65583.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___662_65583.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___662_65583.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___662_65583.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___662_65583.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___662_65583.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___662_65583.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___662_65583.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___662_65583.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___662_65583.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___662_65583.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___662_65583.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___662_65583.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___662_65583.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___662_65583.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___662_65583.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___662_65583.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___662_65583.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___662_65583.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___662_65583.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___662_65583.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___662_65583.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___662_65583.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___662_65583.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___662_65583.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___662_65583.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____65585 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____65585 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____65628 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____65665 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____65699 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____65710 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____65721 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___585_65739  ->
    match uu___585_65739 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____65751 = FStar_Syntax_Util.head_and_args t  in
    match uu____65751 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____65814 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____65816 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____65831 =
                     let uu____65833 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____65833  in
                   FStar_Util.format1 "@<%s>" uu____65831
                in
             let uu____65837 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____65814 uu____65816 uu____65837
         | uu____65840 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___586_65852  ->
      match uu___586_65852 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____65857 =
            let uu____65861 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____65863 =
              let uu____65867 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____65869 =
                let uu____65873 =
                  let uu____65877 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____65877]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____65873
                 in
              uu____65867 :: uu____65869  in
            uu____65861 :: uu____65863  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____65857
      | FStar_TypeChecker_Common.CProb p ->
          let uu____65888 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____65890 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____65892 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____65888
            uu____65890 (rel_to_string p.FStar_TypeChecker_Common.relation)
            uu____65892
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___587_65906  ->
      match uu___587_65906 with
      | UNIV (u,t) ->
          let x =
            let uu____65912 = FStar_Options.hide_uvar_nums ()  in
            if uu____65912
            then "?"
            else
              (let uu____65919 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____65919 FStar_Util.string_of_int)
             in
          let uu____65923 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____65923
      | TERM (u,t) ->
          let x =
            let uu____65930 = FStar_Options.hide_uvar_nums ()  in
            if uu____65930
            then "?"
            else
              (let uu____65937 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____65937 FStar_Util.string_of_int)
             in
          let uu____65941 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____65941
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____65960 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____65960 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____65981 =
      let uu____65985 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____65985
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____65981 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____66004 .
    (FStar_Syntax_Syntax.term * 'Auu____66004) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____66023 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____66044  ->
              match uu____66044 with
              | (x,uu____66051) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____66023 (FStar_String.concat " ")
  
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
        (let uu____66094 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____66094
         then
           let uu____66099 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____66099
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___588_66110  ->
    match uu___588_66110 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____66116 .
    'Auu____66116 FStar_TypeChecker_Common.problem ->
      'Auu____66116 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___722_66128 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___722_66128.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___722_66128.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___722_66128.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___722_66128.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___722_66128.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___722_66128.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___722_66128.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____66136 .
    'Auu____66136 FStar_TypeChecker_Common.problem ->
      'Auu____66136 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___589_66156  ->
    match uu___589_66156 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66162  -> FStar_TypeChecker_Common.TProb _66162)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _66168  -> FStar_TypeChecker_Common.CProb _66168)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___590_66174  ->
    match uu___590_66174 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___734_66180 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___734_66180.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___734_66180.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___734_66180.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___734_66180.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___734_66180.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___734_66180.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___734_66180.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___734_66180.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___734_66180.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___738_66188 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___738_66188.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___738_66188.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___738_66188.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___738_66188.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___738_66188.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___738_66188.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___738_66188.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___738_66188.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___738_66188.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___591_66201  ->
      match uu___591_66201 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___592_66208  ->
    match uu___592_66208 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___593_66221  ->
    match uu___593_66221 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___594_66236  ->
    match uu___594_66236 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___595_66251  ->
    match uu___595_66251 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___596_66265  ->
    match uu___596_66265 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___597_66279  ->
    match uu___597_66279 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___598_66291  ->
    match uu___598_66291 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____66307 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____66307) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____66337 =
          let uu____66339 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66339  in
        if uu____66337
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____66376)::bs ->
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
          let uu____66423 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66447 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66447]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66423
      | FStar_TypeChecker_Common.CProb p ->
          let uu____66475 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____66499 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____66499]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____66475
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____66546 =
          let uu____66548 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66548  in
        if uu____66546
        then ()
        else
          (let uu____66553 =
             let uu____66556 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____66556
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____66553 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____66605 =
          let uu____66607 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____66607  in
        if uu____66605
        then ()
        else
          (let uu____66612 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____66612)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____66632 =
        let uu____66634 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____66634  in
      if uu____66632
      then ()
      else
        (let msgf m =
           let uu____66648 =
             let uu____66650 =
               let uu____66652 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____66652 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____66650  in
           Prims.op_Hat msg uu____66648  in
         (let uu____66657 = msgf "scope"  in
          let uu____66660 = p_scope prob  in
          def_scope_wf uu____66657 (p_loc prob) uu____66660);
         (let uu____66672 = msgf "guard"  in
          def_check_scoped uu____66672 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____66679 = msgf "lhs"  in
                def_check_scoped uu____66679 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66682 = msgf "rhs"  in
                def_check_scoped uu____66682 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____66689 = msgf "lhs"  in
                def_check_scoped_comp uu____66689 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____66692 = msgf "rhs"  in
                def_check_scoped_comp uu____66692 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___831_66713 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___831_66713.wl_deferred);
          ctr = (uu___831_66713.ctr);
          defer_ok = (uu___831_66713.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___831_66713.umax_heuristic_ok);
          tcenv = (uu___831_66713.tcenv);
          wl_implicits = (uu___831_66713.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____66721 .
    FStar_TypeChecker_Env.env ->
      ('Auu____66721 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___835_66744 = empty_worklist env  in
      let uu____66745 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____66745;
        wl_deferred = (uu___835_66744.wl_deferred);
        ctr = (uu___835_66744.ctr);
        defer_ok = (uu___835_66744.defer_ok);
        smt_ok = (uu___835_66744.smt_ok);
        umax_heuristic_ok = (uu___835_66744.umax_heuristic_ok);
        tcenv = (uu___835_66744.tcenv);
        wl_implicits = (uu___835_66744.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___840_66768 = wl  in
        {
          attempting = (uu___840_66768.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___840_66768.ctr);
          defer_ok = (uu___840_66768.defer_ok);
          smt_ok = (uu___840_66768.smt_ok);
          umax_heuristic_ok = (uu___840_66768.umax_heuristic_ok);
          tcenv = (uu___840_66768.tcenv);
          wl_implicits = (uu___840_66768.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___845_66796 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___845_66796.wl_deferred);
         ctr = (uu___845_66796.ctr);
         defer_ok = (uu___845_66796.defer_ok);
         smt_ok = (uu___845_66796.smt_ok);
         umax_heuristic_ok = (uu___845_66796.umax_heuristic_ok);
         tcenv = (uu___845_66796.tcenv);
         wl_implicits = (uu___845_66796.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____66810 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____66810 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____66844 = FStar_Syntax_Util.type_u ()  in
            match uu____66844 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____66856 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____66856 with
                 | (uu____66874,tt,wl1) ->
                     let uu____66877 = FStar_Syntax_Util.mk_eq2 u tt t1 t2
                        in
                     (uu____66877, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___599_66883  ->
    match uu___599_66883 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _66889  -> FStar_TypeChecker_Common.TProb _66889) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _66895  -> FStar_TypeChecker_Common.CProb _66895) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____66903 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____66903 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____66923  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____67020 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____67020 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____67020 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____67020 FStar_TypeChecker_Common.problem *
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
                        let uu____67107 =
                          let uu____67116 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67116]  in
                        FStar_List.append scope uu____67107
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____67159 =
                      let uu____67162 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____67162  in
                    FStar_List.append uu____67159
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____67181 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67181 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____67207 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67207;
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
                  (let uu____67281 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67281 with
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
                  (let uu____67369 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____67369 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____67407 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____67407 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____67407 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____67407 FStar_TypeChecker_Common.problem *
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
                          let uu____67475 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____67475]  in
                        let uu____67494 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____67494
                     in
                  let uu____67497 =
                    let uu____67504 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___928_67515 = wl  in
                       {
                         attempting = (uu___928_67515.attempting);
                         wl_deferred = (uu___928_67515.wl_deferred);
                         ctr = (uu___928_67515.ctr);
                         defer_ok = (uu___928_67515.defer_ok);
                         smt_ok = (uu___928_67515.smt_ok);
                         umax_heuristic_ok =
                           (uu___928_67515.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___928_67515.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____67504
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____67497 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____67533 =
                              let uu____67538 =
                                let uu____67539 =
                                  let uu____67548 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____67548
                                   in
                                [uu____67539]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____67538
                               in
                            uu____67533 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____67578 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____67578;
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
                let uu____67626 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____67626;
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
  'Auu____67641 .
    worklist ->
      'Auu____67641 FStar_TypeChecker_Common.problem ->
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
              let uu____67674 =
                let uu____67677 =
                  let uu____67678 =
                    let uu____67685 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____67685)  in
                  FStar_Syntax_Syntax.NT uu____67678  in
                [uu____67677]  in
              FStar_Syntax_Subst.subst uu____67674 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____67709 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____67709
        then
          let uu____67717 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____67720 = prob_to_string env d  in
          let uu____67722 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____67717 uu____67720 uu____67722 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____67738 -> failwith "impossible"  in
           let uu____67741 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____67757 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67759 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67757, uu____67759)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____67766 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____67768 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____67766, uu____67768)
              in
           match uu____67741 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___600_67796  ->
            match uu___600_67796 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____67808 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____67812 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____67812 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___601_67843  ->
           match uu___601_67843 with
           | UNIV uu____67846 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____67853 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____67853
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
        (fun uu___602_67881  ->
           match uu___602_67881 with
           | UNIV (u',t) ->
               let uu____67886 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____67886
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____67893 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67905 =
        let uu____67906 =
          let uu____67907 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____67907
           in
        FStar_Syntax_Subst.compress uu____67906  in
      FStar_All.pipe_right uu____67905 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67919 =
        let uu____67920 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____67920  in
      FStar_All.pipe_right uu____67919 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67928 = FStar_Syntax_Util.head_and_args t  in
    match uu____67928 with
    | (h,uu____67947) ->
        let uu____67972 =
          let uu____67973 = FStar_Syntax_Subst.compress h  in
          uu____67973.FStar_Syntax_Syntax.n  in
        (match uu____67972 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____67978 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67991 = should_strongly_reduce t  in
      if uu____67991
      then
        let uu____67994 =
          let uu____67995 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____67995  in
        FStar_All.pipe_right uu____67994 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____68005 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____68005) ->
        (FStar_Syntax_Syntax.term * 'Auu____68005)
  =
  fun env  ->
    fun t  ->
      let uu____68028 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____68028, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____68080  ->
              match uu____68080 with
              | (x,imp) ->
                  let uu____68099 =
                    let uu___1025_68100 = x  in
                    let uu____68101 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1025_68100.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1025_68100.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____68101
                    }  in
                  (uu____68099, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____68125 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____68125
        | FStar_Syntax_Syntax.U_max us ->
            let uu____68129 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____68129
        | uu____68132 -> u2  in
      let uu____68133 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____68133
  
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
                (let uu____68254 = norm_refinement env t12  in
                 match uu____68254 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____68269;
                     FStar_Syntax_Syntax.vars = uu____68270;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____68294 =
                       let uu____68296 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____68298 = FStar_Syntax_Print.tag_of_term tt
                          in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____68296 uu____68298
                        in
                     failwith uu____68294)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____68314 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____68314
          | FStar_Syntax_Syntax.Tm_uinst uu____68315 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68352 =
                   let uu____68353 = FStar_Syntax_Subst.compress t1'  in
                   uu____68353.FStar_Syntax_Syntax.n  in
                 match uu____68352 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68368 -> aux true t1'
                 | uu____68376 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____68391 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68422 =
                   let uu____68423 = FStar_Syntax_Subst.compress t1'  in
                   uu____68423.FStar_Syntax_Syntax.n  in
                 match uu____68422 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68438 -> aux true t1'
                 | uu____68446 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____68461 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____68508 =
                   let uu____68509 = FStar_Syntax_Subst.compress t1'  in
                   uu____68509.FStar_Syntax_Syntax.n  in
                 match uu____68508 with
                 | FStar_Syntax_Syntax.Tm_refine uu____68524 -> aux true t1'
                 | uu____68532 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____68547 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____68562 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____68577 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____68592 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____68607 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____68636 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____68669 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____68690 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____68717 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____68745 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____68782 ->
              let uu____68789 =
                let uu____68791 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68793 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68791 uu____68793
                 in
              failwith uu____68789
          | FStar_Syntax_Syntax.Tm_ascribed uu____68808 ->
              let uu____68835 =
                let uu____68837 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68839 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68837 uu____68839
                 in
              failwith uu____68835
          | FStar_Syntax_Syntax.Tm_delayed uu____68854 ->
              let uu____68877 =
                let uu____68879 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68881 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68879 uu____68881
                 in
              failwith uu____68877
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____68896 =
                let uu____68898 = FStar_Syntax_Print.term_to_string t12  in
                let uu____68900 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____68898 uu____68900
                 in
              failwith uu____68896
           in
        let uu____68915 = whnf env t1  in aux false uu____68915
  
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
      let uu____68976 = base_and_refinement env t  in
      FStar_All.pipe_right uu____68976 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____69017 = FStar_Syntax_Syntax.null_bv t  in
    (uu____69017, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____69044 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____69044 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____69104  ->
    match uu____69104 with
    | (t_base,refopt) ->
        let uu____69135 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____69135 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____69177 =
      let uu____69181 =
        let uu____69184 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____69211  ->
                  match uu____69211 with | (uu____69220,uu____69221,x) -> x))
           in
        FStar_List.append wl.attempting uu____69184  in
      FStar_List.map (wl_prob_to_string wl) uu____69181  in
    FStar_All.pipe_right uu____69177 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____69244 .
    ('Auu____69244 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____69256  ->
    match uu____69256 with
    | (uu____69263,c,args) ->
        let uu____69266 = print_ctx_uvar c  in
        let uu____69268 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____69266 uu____69268
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____69278 = FStar_Syntax_Util.head_and_args t  in
    match uu____69278 with
    | (head1,_args) ->
        let uu____69322 =
          let uu____69323 = FStar_Syntax_Subst.compress head1  in
          uu____69323.FStar_Syntax_Syntax.n  in
        (match uu____69322 with
         | FStar_Syntax_Syntax.Tm_uvar uu____69327 -> true
         | uu____69341 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____69349 = FStar_Syntax_Util.head_and_args t  in
    match uu____69349 with
    | (head1,_args) ->
        let uu____69392 =
          let uu____69393 = FStar_Syntax_Subst.compress head1  in
          uu____69393.FStar_Syntax_Syntax.n  in
        (match uu____69392 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____69397) -> u
         | uu____69414 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____69439 = FStar_Syntax_Util.head_and_args t  in
      match uu____69439 with
      | (head1,args) ->
          let uu____69486 =
            let uu____69487 = FStar_Syntax_Subst.compress head1  in
            uu____69487.FStar_Syntax_Syntax.n  in
          (match uu____69486 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____69495)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____69528 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___603_69553  ->
                         match uu___603_69553 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____69558 =
                               let uu____69559 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____69559.FStar_Syntax_Syntax.n  in
                             (match uu____69558 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____69564 -> false)
                         | uu____69566 -> true))
                  in
               (match uu____69528 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____69591 =
                        FStar_List.collect
                          (fun uu___604_69603  ->
                             match uu___604_69603 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____69607 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____69607]
                             | uu____69608 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____69591 FStar_List.rev  in
                    let uu____69631 =
                      let uu____69638 =
                        let uu____69647 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___605_69669  ->
                                  match uu___605_69669 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____69673 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____69673]
                                  | uu____69674 -> []))
                           in
                        FStar_All.pipe_right uu____69647 FStar_List.rev  in
                      let uu____69697 =
                        let uu____69700 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____69700  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____69638 uu____69697
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____69631 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____69736  ->
                                match uu____69736 with
                                | (x,i) ->
                                    let uu____69755 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____69755, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____69786  ->
                                match uu____69786 with
                                | (a,i) ->
                                    let uu____69805 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____69805, i)) args_sol
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
           | uu____69827 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____69849 =
          let uu____69872 =
            let uu____69873 = FStar_Syntax_Subst.compress k  in
            uu____69873.FStar_Syntax_Syntax.n  in
          match uu____69872 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____69955 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____69955)
              else
                (let uu____69990 = FStar_Syntax_Util.abs_formals t  in
                 match uu____69990 with
                 | (ys',t1,uu____70023) ->
                     let uu____70028 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____70028))
          | uu____70067 ->
              let uu____70068 =
                let uu____70073 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____70073)  in
              ((ys, t), uu____70068)
           in
        match uu____69849 with
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
                 let uu____70168 = FStar_Syntax_Util.rename_binders xs ys1
                    in
                 FStar_Syntax_Subst.subst_comp uu____70168 c  in
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
               (let uu____70246 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70246
                then
                  let uu____70251 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____70253 = print_ctx_uvar uv  in
                  let uu____70255 = FStar_Syntax_Print.term_to_string phi1
                     in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____70251 uu____70253 uu____70255
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____70264 =
                   let uu____70266 = FStar_Util.string_of_int (p_pid prob)
                      in
                   Prims.op_Hat "solve_prob'.sol." uu____70266  in
                 let uu____70269 =
                   let uu____70272 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____70272
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____70264 uu____70269 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____70305 =
               let uu____70306 =
                 let uu____70308 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____70310 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____70308 uu____70310
                  in
               failwith uu____70306  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____70376  ->
                       match uu____70376 with
                       | (a,i) ->
                           let uu____70397 =
                             let uu____70398 = FStar_Syntax_Subst.compress a
                                in
                             uu____70398.FStar_Syntax_Syntax.n  in
                           (match uu____70397 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____70424 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____70434 =
                 let uu____70436 = is_flex g  in
                 Prims.op_Negation uu____70436  in
               if uu____70434
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____70445 = destruct_flex_t g wl  in
                  match uu____70445 with
                  | ((uu____70450,uv1,args),wl1) ->
                      ((let uu____70455 = args_as_binders args  in
                        assign_solution uu____70455 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___1277_70457 = wl1  in
              {
                attempting = (uu___1277_70457.attempting);
                wl_deferred = (uu___1277_70457.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___1277_70457.defer_ok);
                smt_ok = (uu___1277_70457.smt_ok);
                umax_heuristic_ok = (uu___1277_70457.umax_heuristic_ok);
                tcenv = (uu___1277_70457.tcenv);
                wl_implicits = (uu___1277_70457.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____70482 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____70482
         then
           let uu____70487 = FStar_Util.string_of_int pid  in
           let uu____70489 =
             let uu____70491 = FStar_List.map (uvi_to_string wl.tcenv) sol
                in
             FStar_All.pipe_right uu____70491 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____70487
             uu____70489
         else ());
        commit sol;
        (let uu___1285_70505 = wl  in
         {
           attempting = (uu___1285_70505.attempting);
           wl_deferred = (uu___1285_70505.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___1285_70505.defer_ok);
           smt_ok = (uu___1285_70505.smt_ok);
           umax_heuristic_ok = (uu___1285_70505.umax_heuristic_ok);
           tcenv = (uu___1285_70505.tcenv);
           wl_implicits = (uu___1285_70505.wl_implicits)
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
             | (uu____70571,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____70599 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____70599
              in
           (let uu____70605 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____70605
            then
              let uu____70610 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____70614 =
                let uu____70616 =
                  FStar_List.map (uvi_to_string wl.tcenv) uvis  in
                FStar_All.pipe_right uu____70616 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____70610
                uu____70614
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
        let uu____70651 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____70651 FStar_Util.set_elements  in
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
      let uu____70691 = occurs uk t  in
      match uu____70691 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____70730 =
                 let uu____70732 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____70734 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____70732 uu____70734
                  in
               FStar_Pervasives_Native.Some uu____70730)
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
            let uu____70854 = maximal_prefix bs_tail bs'_tail  in
            (match uu____70854 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____70905 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____70962  ->
             match uu____70962 with
             | (x,uu____70974) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____70992 = FStar_List.last bs  in
      match uu____70992 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____71016) ->
          let uu____71027 =
            FStar_Util.prefix_until
              (fun uu___606_71042  ->
                 match uu___606_71042 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____71045 -> false) g
             in
          (match uu____71027 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____71059,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____71096 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____71096 with
        | (pfx,uu____71106) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____71118 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____71118 with
             | (uu____71126,src',wl1) ->
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
                 | uu____71240 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____71241 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____71305  ->
                  fun uu____71306  ->
                    match (uu____71305, uu____71306) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____71409 =
                          let uu____71411 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____71411
                           in
                        if uu____71409
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____71445 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____71445
                           then
                             let uu____71462 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____71462)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____71241 with | (isect,uu____71512) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____71548 'Auu____71549 .
    (FStar_Syntax_Syntax.bv * 'Auu____71548) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____71549) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____71607  ->
              fun uu____71608  ->
                match (uu____71607, uu____71608) with
                | ((a,uu____71627),(b,uu____71629)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____71645 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____71645) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____71676  ->
           match uu____71676 with
           | (y,uu____71683) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____71693 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____71693) Prims.list ->
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
                   let uu____71855 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____71855
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____71888 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____71940 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____71985 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____72007 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___607_72015  ->
    match uu___607_72015 with
    | MisMatch (d1,d2) ->
        let uu____72027 =
          let uu____72029 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____72031 =
            let uu____72033 =
              let uu____72035 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____72035 ")"  in
            Prims.op_Hat ") (" uu____72033  in
          Prims.op_Hat uu____72029 uu____72031  in
        Prims.op_Hat "MisMatch (" uu____72027
    | HeadMatch u ->
        let uu____72042 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____72042
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___608_72051  ->
    match uu___608_72051 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____72068 -> HeadMatch false
  
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
          let uu____72090 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____72090 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____72101 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____72125 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____72135 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____72162 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____72162
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____72163 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____72164 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____72165 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____72178 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____72192 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____72216) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72222,uu____72223) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____72265) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____72290;
             FStar_Syntax_Syntax.index = uu____72291;
             FStar_Syntax_Syntax.sort = t2;_},uu____72293)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____72301 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____72302 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____72303 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____72318 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____72325 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____72345 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____72345
  
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
           { FStar_Syntax_Syntax.blob = uu____72364;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72365;
             FStar_Syntax_Syntax.ltyp = uu____72366;
             FStar_Syntax_Syntax.rng = uu____72367;_},uu____72368)
            ->
            let uu____72379 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____72379 t21
        | (uu____72380,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____72381;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____72382;
             FStar_Syntax_Syntax.ltyp = uu____72383;
             FStar_Syntax_Syntax.rng = uu____72384;_})
            ->
            let uu____72395 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____72395
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____72407 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____72407
            then FullMatch
            else
              (let uu____72412 =
                 let uu____72421 =
                   let uu____72424 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____72424  in
                 let uu____72425 =
                   let uu____72428 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____72428  in
                 (uu____72421, uu____72425)  in
               MisMatch uu____72412)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____72434),FStar_Syntax_Syntax.Tm_uinst (g,uu____72436)) ->
            let uu____72445 = head_matches env f g  in
            FStar_All.pipe_right uu____72445 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____72446) -> HeadMatch true
        | (uu____72448,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____72452 = FStar_Const.eq_const c d  in
            if uu____72452
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____72462),FStar_Syntax_Syntax.Tm_uvar (uv',uu____72464)) ->
            let uu____72497 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____72497
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____72507),FStar_Syntax_Syntax.Tm_refine (y,uu____72509)) ->
            let uu____72518 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72518 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____72520),uu____72521) ->
            let uu____72526 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____72526 head_match
        | (uu____72527,FStar_Syntax_Syntax.Tm_refine (x,uu____72529)) ->
            let uu____72534 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____72534 head_match
        | (FStar_Syntax_Syntax.Tm_type
           uu____72535,FStar_Syntax_Syntax.Tm_type uu____72536) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____72538,FStar_Syntax_Syntax.Tm_arrow uu____72539) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____72570),FStar_Syntax_Syntax.Tm_app
           (head',uu____72572)) ->
            let uu____72621 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____72621 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____72623),uu____72624) ->
            let uu____72649 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____72649 head_match
        | (uu____72650,FStar_Syntax_Syntax.Tm_app (head1,uu____72652)) ->
            let uu____72677 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____72677 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____72678,FStar_Syntax_Syntax.Tm_let
           uu____72679) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____72707,FStar_Syntax_Syntax.Tm_match uu____72708) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____72754,FStar_Syntax_Syntax.Tm_abs
           uu____72755) -> HeadMatch true
        | uu____72793 ->
            let uu____72798 =
              let uu____72807 = delta_depth_of_term env t11  in
              let uu____72810 = delta_depth_of_term env t21  in
              (uu____72807, uu____72810)  in
            MisMatch uu____72798
  
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
            (let uu____72876 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____72876
             then
               let uu____72881 = FStar_Syntax_Print.term_to_string t  in
               let uu____72883 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____72881 uu____72883
             else ());
            (let uu____72888 =
               let uu____72889 = FStar_Syntax_Util.un_uinst head1  in
               uu____72889.FStar_Syntax_Syntax.n  in
             match uu____72888 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72895 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____72895 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____72909 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____72909
                        then
                          let uu____72914 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____72914
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____72919 ->
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
                      let uu____72936 =
                        let uu____72938 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____72938 = FStar_Syntax_Util.Equal  in
                      if uu____72936
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____72945 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____72945
                          then
                            let uu____72950 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____72952 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n"
                              uu____72950 uu____72952
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____72957 -> FStar_Pervasives_Native.None)
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
            (let uu____73109 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____73109
             then
               let uu____73114 = FStar_Syntax_Print.term_to_string t11  in
               let uu____73116 = FStar_Syntax_Print.term_to_string t21  in
               let uu____73118 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____73114
                 uu____73116 uu____73118
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____73146 =
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
               match uu____73146 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____73194 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____73194 with
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
                  uu____73232),uu____73233)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73254 =
                      let uu____73263 = maybe_inline t11  in
                      let uu____73266 = maybe_inline t21  in
                      (uu____73263, uu____73266)  in
                    match uu____73254 with
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
                 (uu____73309,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____73310))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____73331 =
                      let uu____73340 = maybe_inline t11  in
                      let uu____73343 = maybe_inline t21  in
                      (uu____73340, uu____73343)  in
                    match uu____73331 with
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
             | MisMatch uu____73398 -> fail1 n_delta r t11 t21
             | uu____73407 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____73422 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____73422
           then
             let uu____73427 = FStar_Syntax_Print.term_to_string t1  in
             let uu____73429 = FStar_Syntax_Print.term_to_string t2  in
             let uu____73431 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____73439 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____73456 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____73456
                    (fun uu____73491  ->
                       match uu____73491 with
                       | (t11,t21) ->
                           let uu____73499 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____73501 =
                             let uu____73503 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____73503  in
                           Prims.op_Hat uu____73499 uu____73501))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____73427 uu____73429 uu____73431 uu____73439
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____73520 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____73520 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___609_73535  ->
    match uu___609_73535 with
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
      let uu___1789_73584 = p  in
      let uu____73587 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____73588 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1789_73584.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____73587;
        FStar_TypeChecker_Common.relation =
          (uu___1789_73584.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____73588;
        FStar_TypeChecker_Common.element =
          (uu___1789_73584.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1789_73584.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1789_73584.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1789_73584.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1789_73584.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1789_73584.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____73603 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____73603
            (fun _73608  -> FStar_TypeChecker_Common.TProb _73608)
      | FStar_TypeChecker_Common.CProb uu____73609 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____73632 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____73632 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____73640 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____73640 with
           | (lh,lhs_args) ->
               let uu____73687 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____73687 with
                | (rh,rhs_args) ->
                    let uu____73734 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73747,FStar_Syntax_Syntax.Tm_uvar uu____73748)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____73837 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____73864,uu____73865)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____73880,FStar_Syntax_Syntax.Tm_uvar uu____73881)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73896,FStar_Syntax_Syntax.Tm_arrow
                         uu____73897) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_73927 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_73927.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_73927.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_73927.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_73927.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_73927.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_73927.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_73927.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_73927.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_73927.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____73930,FStar_Syntax_Syntax.Tm_type uu____73931)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_73947 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_73947.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_73947.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_73947.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_73947.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_73947.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_73947.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_73947.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_73947.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_73947.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____73950,FStar_Syntax_Syntax.Tm_uvar uu____73951)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1840_73967 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1840_73967.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1840_73967.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1840_73967.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1840_73967.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1840_73967.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1840_73967.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1840_73967.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1840_73967.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1840_73967.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____73970,FStar_Syntax_Syntax.Tm_uvar uu____73971)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____73986,uu____73987)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____74002,FStar_Syntax_Syntax.Tm_uvar uu____74003)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____74018,uu____74019) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____73734 with
                     | (rank,tp1) ->
                         let uu____74032 =
                           FStar_All.pipe_right
                             (let uu___1860_74036 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1860_74036.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1860_74036.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1860_74036.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1860_74036.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1860_74036.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1860_74036.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1860_74036.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1860_74036.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1860_74036.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _74039  ->
                                FStar_TypeChecker_Common.TProb _74039)
                            in
                         (rank, uu____74032))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____74043 =
            FStar_All.pipe_right
              (let uu___1864_74047 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1864_74047.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1864_74047.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1864_74047.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1864_74047.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1864_74047.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1864_74047.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1864_74047.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1864_74047.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1864_74047.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _74050  -> FStar_TypeChecker_Common.CProb _74050)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____74043)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____74110 probs =
      match uu____74110 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____74191 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____74212 = rank wl.tcenv hd1  in
               (match uu____74212 with
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
                      (let uu____74273 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____74278 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____74278)
                          in
                       if uu____74273
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
          let uu____74351 = FStar_Syntax_Util.head_and_args t  in
          match uu____74351 with
          | (hd1,uu____74370) ->
              let uu____74395 =
                let uu____74396 = FStar_Syntax_Subst.compress hd1  in
                uu____74396.FStar_Syntax_Syntax.n  in
              (match uu____74395 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____74401) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____74436  ->
                           match uu____74436 with
                           | (y,uu____74445) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____74468  ->
                                       match uu____74468 with
                                       | (x,uu____74477) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____74482 -> false)
           in
        let uu____74484 = rank tcenv p  in
        match uu____74484 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____74493 -> true
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
    match projectee with | UDeferred _0 -> true | uu____74530 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____74550 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____74571 -> false
  
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
                        let uu____74634 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____74634 with
                        | (k,uu____74642) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____74655 -> false)))
            | uu____74657 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____74709 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____74717 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____74717 = (Prims.parse_int "0")))
                           in
                        if uu____74709 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____74738 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____74746 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____74746 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____74738)
               in
            let uu____74750 = filter1 u12  in
            let uu____74753 = filter1 u22  in (uu____74750, uu____74753)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____74788 = filter_out_common_univs us1 us2  in
                   (match uu____74788 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____74848 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____74848 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____74851 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____74862 =
                             let uu____74864 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____74866 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____74864 uu____74866
                              in
                           UFailed uu____74862))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74892 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74892 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____74918 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____74918 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____74921 ->
                   let uu____74926 =
                     let uu____74928 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____74930 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____74928 uu____74930 msg
                      in
                   UFailed uu____74926)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____74933,uu____74934) ->
              let uu____74936 =
                let uu____74938 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____74940 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____74938 uu____74940
                 in
              failwith uu____74936
          | (FStar_Syntax_Syntax.U_unknown ,uu____74943) ->
              let uu____74944 =
                let uu____74946 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____74948 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____74946 uu____74948
                 in
              failwith uu____74944
          | (uu____74951,FStar_Syntax_Syntax.U_bvar uu____74952) ->
              let uu____74954 =
                let uu____74956 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____74958 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____74956 uu____74958
                 in
              failwith uu____74954
          | (uu____74961,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____74962 =
                let uu____74964 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____74966 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____74964 uu____74966
                 in
              failwith uu____74962
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____74996 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____74996
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____75013 = occurs_univ v1 u3  in
              if uu____75013
              then
                let uu____75016 =
                  let uu____75018 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75020 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75018 uu____75020
                   in
                try_umax_components u11 u21 uu____75016
              else
                (let uu____75025 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75025)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____75037 = occurs_univ v1 u3  in
              if uu____75037
              then
                let uu____75040 =
                  let uu____75042 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____75044 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____75042 uu____75044
                   in
                try_umax_components u11 u21 uu____75040
              else
                (let uu____75049 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____75049)
          | (FStar_Syntax_Syntax.U_max uu____75050,uu____75051) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75059 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75059
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____75065,FStar_Syntax_Syntax.U_max uu____75066) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____75074 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____75074
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____75080,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____75082,FStar_Syntax_Syntax.U_name uu____75083) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____75085) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____75087) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75089,FStar_Syntax_Syntax.U_succ uu____75090) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____75092,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____75199 = bc1  in
      match uu____75199 with
      | (bs1,mk_cod1) ->
          let uu____75243 = bc2  in
          (match uu____75243 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____75354 = aux xs ys  in
                     (match uu____75354 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____75437 =
                       let uu____75444 = mk_cod1 xs  in ([], uu____75444)  in
                     let uu____75447 =
                       let uu____75454 = mk_cod2 ys  in ([], uu____75454)  in
                     (uu____75437, uu____75447)
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
                  let uu____75523 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____75523 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____75526 =
                    let uu____75527 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____75527 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____75526
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____75532 = has_type_guard t1 t2  in (uu____75532, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____75533 = has_type_guard t2 t1  in (uu____75533, wl)
  
let is_flex_pat :
  'Auu____75543 'Auu____75544 'Auu____75545 .
    ('Auu____75543 * 'Auu____75544 * 'Auu____75545 Prims.list) -> Prims.bool
  =
  fun uu___610_75559  ->
    match uu___610_75559 with
    | (uu____75568,uu____75569,[]) -> true
    | uu____75573 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____75606 = f  in
      match uu____75606 with
      | (uu____75613,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____75614;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____75615;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____75618;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____75619;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____75620;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____75621;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____75691  ->
                 match uu____75691 with
                 | (y,uu____75700) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____75854 =
                  let uu____75869 =
                    let uu____75872 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____75872  in
                  ((FStar_List.rev pat_binders), uu____75869)  in
                FStar_Pervasives_Native.Some uu____75854
            | (uu____75905,[]) ->
                let uu____75936 =
                  let uu____75951 =
                    let uu____75954 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____75954  in
                  ((FStar_List.rev pat_binders), uu____75951)  in
                FStar_Pervasives_Native.Some uu____75936
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____76045 =
                  let uu____76046 = FStar_Syntax_Subst.compress a  in
                  uu____76046.FStar_Syntax_Syntax.n  in
                (match uu____76045 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____76066 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____76066
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___2188_76096 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___2188_76096.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___2188_76096.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____76100 =
                            let uu____76101 =
                              let uu____76108 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____76108)  in
                            FStar_Syntax_Syntax.NT uu____76101  in
                          [uu____76100]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___2194_76124 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2194_76124.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2194_76124.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____76125 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____76165 =
                  let uu____76180 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____76180  in
                (match uu____76165 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____76255 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____76288 ->
               let uu____76289 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____76289 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____76611 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____76611
       then
         let uu____76616 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____76616
       else ());
      (let uu____76621 = next_prob probs  in
       match uu____76621 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___2219_76648 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___2219_76648.wl_deferred);
               ctr = (uu___2219_76648.ctr);
               defer_ok = (uu___2219_76648.defer_ok);
               smt_ok = (uu___2219_76648.smt_ok);
               umax_heuristic_ok = (uu___2219_76648.umax_heuristic_ok);
               tcenv = (uu___2219_76648.tcenv);
               wl_implicits = (uu___2219_76648.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____76657 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____76657
                 then
                   let uu____76660 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____76660
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
                           (let uu___2231_76672 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___2231_76672.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___2231_76672.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___2231_76672.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___2231_76672.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___2231_76672.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___2231_76672.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___2231_76672.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___2231_76672.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___2231_76672.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____76698 ->
                let uu____76709 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____76780  ->
                          match uu____76780 with
                          | (c,uu____76791,uu____76792) -> c < probs.ctr))
                   in
                (match uu____76709 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____76847 =
                            let uu____76852 =
                              FStar_List.map
                                (fun uu____76870  ->
                                   match uu____76870 with
                                   | (uu____76884,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____76852, (probs.wl_implicits))  in
                          Success uu____76847
                      | uu____76892 ->
                          let uu____76903 =
                            let uu___2249_76904 = probs  in
                            let uu____76905 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____76928  ->
                                      match uu____76928 with
                                      | (uu____76937,uu____76938,y) -> y))
                               in
                            {
                              attempting = uu____76905;
                              wl_deferred = rest;
                              ctr = (uu___2249_76904.ctr);
                              defer_ok = (uu___2249_76904.defer_ok);
                              smt_ok = (uu___2249_76904.smt_ok);
                              umax_heuristic_ok =
                                (uu___2249_76904.umax_heuristic_ok);
                              tcenv = (uu___2249_76904.tcenv);
                              wl_implicits = (uu___2249_76904.wl_implicits)
                            }  in
                          solve env uu____76903))))

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
            let uu____76949 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____76949 with
            | USolved wl1 ->
                let uu____76951 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____76951
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
                  let uu____77005 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____77005 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____77008 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____77021;
                  FStar_Syntax_Syntax.vars = uu____77022;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____77025;
                  FStar_Syntax_Syntax.vars = uu____77026;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____77039,uu____77040) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____77048,FStar_Syntax_Syntax.Tm_uinst uu____77049) ->
                failwith "Impossible: expect head symbols to match"
            | uu____77057 -> USolved wl

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
            ((let uu____77069 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____77069
              then
                let uu____77074 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____77074 msg
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
               let uu____77166 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____77166 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____77221 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____77221
                then
                  let uu____77226 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____77228 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____77226 uu____77228
                else ());
               (let uu____77233 = head_matches_delta env1 wl2 t1 t2  in
                match uu____77233 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____77279 = eq_prob t1 t2 wl2  in
                         (match uu____77279 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____77300 ->
                         let uu____77309 = eq_prob t1 t2 wl2  in
                         (match uu____77309 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____77359 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____77374 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____77375 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____77374, uu____77375)
                           | FStar_Pervasives_Native.None  ->
                               let uu____77380 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____77381 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____77380, uu____77381)
                            in
                         (match uu____77359 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____77412 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____77412 with
                                | (t1_hd,t1_args) ->
                                    let uu____77457 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____77457 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____77523 =
                                              let uu____77530 =
                                                let uu____77541 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____77541 :: t1_args  in
                                              let uu____77558 =
                                                let uu____77567 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____77567 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____77616  ->
                                                   fun uu____77617  ->
                                                     fun uu____77618  ->
                                                       match (uu____77616,
                                                               uu____77617,
                                                               uu____77618)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____77668),
                                                          (a2,uu____77670))
                                                           ->
                                                           let uu____77707 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____77707
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____77530
                                                uu____77558
                                               in
                                            match uu____77523 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___2403_77733 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___2403_77733.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___2403_77733.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___2403_77733.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____77745 =
                                                  solve env1 wl'  in
                                                (match uu____77745 with
                                                 | Success (uu____77748,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___2412_77752
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___2412_77752.attempting);
                                                            wl_deferred =
                                                              (uu___2412_77752.wl_deferred);
                                                            ctr =
                                                              (uu___2412_77752.ctr);
                                                            defer_ok =
                                                              (uu___2412_77752.defer_ok);
                                                            smt_ok =
                                                              (uu___2412_77752.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___2412_77752.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___2412_77752.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____77753 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____77786 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____77786 with
                                | (t1_base,p1_opt) ->
                                    let uu____77822 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____77822 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____77921 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____77921
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
                                               let uu____77974 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____77974
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
                                               let uu____78006 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78006
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
                                               let uu____78038 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____78038
                                           | uu____78041 -> t_base  in
                                         let uu____78058 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____78058 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____78072 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____78072, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____78079 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____78079 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____78115 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____78115 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____78151 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____78151
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
                              let uu____78175 = combine t11 t21 wl2  in
                              (match uu____78175 with
                               | (t12,ps,wl3) ->
                                   ((let uu____78208 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____78208
                                     then
                                       let uu____78213 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____78213
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____78255 ts1 =
               match uu____78255 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____78318 = pairwise out t wl2  in
                        (match uu____78318 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____78354 =
               let uu____78365 = FStar_List.hd ts  in (uu____78365, [], wl1)
                in
             let uu____78374 = FStar_List.tl ts  in
             aux uu____78354 uu____78374  in
           let uu____78381 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____78381 with
           | (this_flex,this_rigid) ->
               let uu____78407 =
                 let uu____78408 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____78408.FStar_Syntax_Syntax.n  in
               (match uu____78407 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____78433 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____78433
                    then
                      let uu____78436 = destruct_flex_t this_flex wl  in
                      (match uu____78436 with
                       | (flex,wl1) ->
                           let uu____78443 = quasi_pattern env flex  in
                           (match uu____78443 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____78462 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____78462
                                  then
                                    let uu____78467 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____78467
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____78474 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2514_78477 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_78477.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2514_78477.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2514_78477.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_78477.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_78477.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_78477.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_78477.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_78477.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_78477.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____78474)
                | uu____78478 ->
                    ((let uu____78480 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____78480
                      then
                        let uu____78485 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____78485
                      else ());
                     (let uu____78490 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____78490 with
                      | (u,_args) ->
                          let uu____78533 =
                            let uu____78534 = FStar_Syntax_Subst.compress u
                               in
                            uu____78534.FStar_Syntax_Syntax.n  in
                          (match uu____78533 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____78562 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____78562 with
                                 | (u',uu____78581) ->
                                     let uu____78606 =
                                       let uu____78607 = whnf env u'  in
                                       uu____78607.FStar_Syntax_Syntax.n  in
                                     (match uu____78606 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____78629 -> false)
                                  in
                               let uu____78631 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___611_78654  ->
                                         match uu___611_78654 with
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
                                              | uu____78668 -> false)
                                         | uu____78672 -> false))
                                  in
                               (match uu____78631 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____78687 = whnf env this_rigid
                                         in
                                      let uu____78688 =
                                        FStar_List.collect
                                          (fun uu___612_78694  ->
                                             match uu___612_78694 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____78700 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____78700]
                                             | uu____78704 -> [])
                                          bounds_probs
                                         in
                                      uu____78687 :: uu____78688  in
                                    let uu____78705 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____78705 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____78738 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____78753 =
                                               let uu____78754 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____78754.FStar_Syntax_Syntax.n
                                                in
                                             match uu____78753 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____78766 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____78766)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____78777 -> bound  in
                                           let uu____78778 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____78778)  in
                                         (match uu____78738 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____78813 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____78813
                                                then
                                                  let wl'1 =
                                                    let uu___2574_78819 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2574_78819.wl_deferred);
                                                      ctr =
                                                        (uu___2574_78819.ctr);
                                                      defer_ok =
                                                        (uu___2574_78819.defer_ok);
                                                      smt_ok =
                                                        (uu___2574_78819.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2574_78819.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2574_78819.tcenv);
                                                      wl_implicits =
                                                        (uu___2574_78819.wl_implicits)
                                                    }  in
                                                  let uu____78820 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____78820
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____78826 =
                                                  solve_t env eq_prob
                                                    (let uu___2579_78828 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2579_78828.wl_deferred);
                                                       ctr =
                                                         (uu___2579_78828.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2579_78828.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2579_78828.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2579_78828.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____78826 with
                                                | Success (uu____78830,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2585_78833 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2585_78833.wl_deferred);
                                                        ctr =
                                                          (uu___2585_78833.ctr);
                                                        defer_ok =
                                                          (uu___2585_78833.defer_ok);
                                                        smt_ok =
                                                          (uu___2585_78833.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2585_78833.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2585_78833.tcenv);
                                                        wl_implicits =
                                                          (uu___2585_78833.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2588_78835 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2588_78835.attempting);
                                                        wl_deferred =
                                                          (uu___2588_78835.wl_deferred);
                                                        ctr =
                                                          (uu___2588_78835.ctr);
                                                        defer_ok =
                                                          (uu___2588_78835.defer_ok);
                                                        smt_ok =
                                                          (uu___2588_78835.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2588_78835.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2588_78835.tcenv);
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
                                                    let uu____78851 =
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
                                                    ((let uu____78865 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____78865
                                                      then
                                                        let uu____78870 =
                                                          let uu____78872 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____78872
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____78870
                                                      else ());
                                                     (let uu____78885 =
                                                        let uu____78900 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____78900)
                                                         in
                                                      match uu____78885 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____78922))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____78948 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____78948
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
                                                                  let uu____78968
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____78968))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____78993 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____78993
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
                                                                    let uu____79013
                                                                    =
                                                                    let uu____79018
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____79018
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____79013
                                                                    [] wl2
                                                                     in
                                                                  let uu____79024
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____79024))))
                                                      | uu____79025 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____79041 when flip ->
                               let uu____79042 =
                                 let uu____79044 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79046 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____79044 uu____79046
                                  in
                               failwith uu____79042
                           | uu____79049 ->
                               let uu____79050 =
                                 let uu____79052 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____79054 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____79052 uu____79054
                                  in
                               failwith uu____79050)))))

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
                      (fun uu____79090  ->
                         match uu____79090 with
                         | (x,i) ->
                             let uu____79109 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____79109, i)) bs_lhs
                     in
                  let uu____79112 = lhs  in
                  match uu____79112 with
                  | (uu____79113,u_lhs,uu____79115) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____79212 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____79222 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____79222, univ)
                             in
                          match uu____79212 with
                          | (k,univ) ->
                              let uu____79229 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____79229 with
                               | (uu____79246,u,wl3) ->
                                   let uu____79249 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____79249, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____79275 =
                              let uu____79288 =
                                let uu____79299 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____79299 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____79350  ->
                                   fun uu____79351  ->
                                     match (uu____79350, uu____79351) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____79452 =
                                           let uu____79459 =
                                             let uu____79462 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____79462
                                              in
                                           copy_uvar u_lhs [] uu____79459 wl2
                                            in
                                         (match uu____79452 with
                                          | (uu____79491,t_a,wl3) ->
                                              let uu____79494 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____79494 with
                                               | (uu____79513,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____79288
                                ([], wl1)
                               in
                            (match uu____79275 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2698_79569 = ct  in
                                   let uu____79570 =
                                     let uu____79573 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____79573
                                      in
                                   let uu____79588 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2698_79569.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2698_79569.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____79570;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____79588;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2698_79569.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2701_79606 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2701_79606.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2701_79606.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____79609 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____79609 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____79671 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____79671 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____79682 =
                                          let uu____79687 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____79687)  in
                                        TERM uu____79682  in
                                      let uu____79688 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____79688 with
                                       | (sub_prob,wl3) ->
                                           let uu____79702 =
                                             let uu____79703 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____79703
                                              in
                                           solve env uu____79702))
                             | (x,imp)::formals2 ->
                                 let uu____79725 =
                                   let uu____79732 =
                                     let uu____79735 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____79735
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____79732 wl1
                                    in
                                 (match uu____79725 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____79756 =
                                          let uu____79759 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____79759
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____79756 u_x
                                         in
                                      let uu____79760 =
                                        let uu____79763 =
                                          let uu____79766 =
                                            let uu____79767 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____79767, imp)  in
                                          [uu____79766]  in
                                        FStar_List.append bs_terms
                                          uu____79763
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____79760 formals2 wl2)
                              in
                           let uu____79794 = occurs_check u_lhs arrow1  in
                           (match uu____79794 with
                            | (uu____79807,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____79823 =
                                    let uu____79825 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____79825
                                     in
                                  giveup_or_defer env orig wl uu____79823
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
              (let uu____79858 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____79858
               then
                 let uu____79863 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____79866 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____79863 (rel_to_string (p_rel orig)) uu____79866
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____79993 = rhs wl1 scope env1 subst1  in
                     (match uu____79993 with
                      | (rhs_prob,wl2) ->
                          ((let uu____80014 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____80014
                            then
                              let uu____80019 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____80019
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____80097 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____80097 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2770_80099 = hd1  in
                       let uu____80100 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2770_80099.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2770_80099.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80100
                       }  in
                     let hd21 =
                       let uu___2773_80104 = hd2  in
                       let uu____80105 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2773_80104.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2773_80104.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____80105
                       }  in
                     let uu____80108 =
                       let uu____80113 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____80113
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____80108 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____80134 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____80134
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____80141 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____80141 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____80208 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____80208
                                  in
                               ((let uu____80226 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____80226
                                 then
                                   let uu____80231 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____80233 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____80231
                                     uu____80233
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____80266 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____80302 = aux wl [] env [] bs1 bs2  in
               match uu____80302 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____80357 = attempt sub_probs wl2  in
                   solve env uu____80357)

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
            let uu___2808_80378 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2808_80378.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2808_80378.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____80391 = try_solve env wl'  in
          match uu____80391 with
          | Success (uu____80392,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2817_80396 = wl  in
                  {
                    attempting = (uu___2817_80396.attempting);
                    wl_deferred = (uu___2817_80396.wl_deferred);
                    ctr = (uu___2817_80396.ctr);
                    defer_ok = (uu___2817_80396.defer_ok);
                    smt_ok = (uu___2817_80396.smt_ok);
                    umax_heuristic_ok = (uu___2817_80396.umax_heuristic_ok);
                    tcenv = (uu___2817_80396.tcenv);
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
        (let uu____80408 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____80408 wl)

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
              let uu____80422 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____80422 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____80456 = lhs1  in
              match uu____80456 with
              | (uu____80459,ctx_u,uu____80461) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____80469 ->
                        let uu____80470 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____80470 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____80519 = quasi_pattern env1 lhs1  in
              match uu____80519 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____80553) ->
                  let uu____80558 = lhs1  in
                  (match uu____80558 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____80573 = occurs_check ctx_u rhs1  in
                       (match uu____80573 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____80624 =
                                let uu____80632 =
                                  let uu____80634 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____80634
                                   in
                                FStar_Util.Inl uu____80632  in
                              (uu____80624, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____80662 =
                                 let uu____80664 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____80664  in
                               if uu____80662
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____80691 =
                                    let uu____80699 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____80699  in
                                  let uu____80705 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____80691, uu____80705)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____80749 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____80749 with
              | (rhs_hd,args) ->
                  let uu____80792 = FStar_Util.prefix args  in
                  (match uu____80792 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____80864 = lhs1  in
                       (match uu____80864 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____80868 =
                              let uu____80879 =
                                let uu____80886 =
                                  let uu____80889 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____80889
                                   in
                                copy_uvar u_lhs [] uu____80886 wl1  in
                              match uu____80879 with
                              | (uu____80916,t_last_arg,wl2) ->
                                  let uu____80919 =
                                    let uu____80926 =
                                      let uu____80927 =
                                        let uu____80936 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____80936]  in
                                      FStar_List.append bs_lhs uu____80927
                                       in
                                    copy_uvar u_lhs uu____80926 t_res_lhs wl2
                                     in
                                  (match uu____80919 with
                                   | (uu____80971,lhs',wl3) ->
                                       let uu____80974 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____80974 with
                                        | (uu____80991,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____80868 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____81012 =
                                     let uu____81013 =
                                       let uu____81018 =
                                         let uu____81019 =
                                           let uu____81022 =
                                             let uu____81027 =
                                               let uu____81028 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____81028]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____81027
                                              in
                                           uu____81022
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____81019
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____81018)  in
                                     TERM uu____81013  in
                                   [uu____81012]  in
                                 let uu____81055 =
                                   let uu____81062 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____81062 with
                                   | (p1,wl3) ->
                                       let uu____81082 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____81082 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____81055 with
                                  | (sub_probs,wl3) ->
                                      let uu____81114 =
                                        let uu____81115 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____81115  in
                                      solve env1 uu____81114))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____81149 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____81149 with
                | (uu____81167,args) ->
                    (match args with | [] -> false | uu____81203 -> true)
                 in
              let is_arrow rhs2 =
                let uu____81222 =
                  let uu____81223 = FStar_Syntax_Subst.compress rhs2  in
                  uu____81223.FStar_Syntax_Syntax.n  in
                match uu____81222 with
                | FStar_Syntax_Syntax.Tm_arrow uu____81227 -> true
                | uu____81243 -> false  in
              let uu____81245 = quasi_pattern env1 lhs1  in
              match uu____81245 with
              | FStar_Pervasives_Native.None  ->
                  let uu____81256 =
                    let uu____81258 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____81258
                     in
                  giveup_or_defer env1 orig1 wl1 uu____81256
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____81267 = is_app rhs1  in
                  if uu____81267
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____81272 = is_arrow rhs1  in
                     if uu____81272
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____81277 =
                          let uu____81279 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____81279
                           in
                        giveup_or_defer env1 orig1 wl1 uu____81277))
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
                let uu____81290 = lhs  in
                (match uu____81290 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____81294 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____81294 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____81312 =
                              let uu____81316 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____81316
                               in
                            FStar_All.pipe_right uu____81312
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____81337 = occurs_check ctx_uv rhs1  in
                          (match uu____81337 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____81366 =
                                   let uu____81368 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____81368
                                    in
                                 giveup_or_defer env orig wl uu____81366
                               else
                                 (let uu____81374 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____81374
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____81381 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____81381
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____81385 =
                                         let uu____81387 =
                                           names_to_string1 fvs2  in
                                         let uu____81389 =
                                           names_to_string1 fvs1  in
                                         let uu____81391 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____81387 uu____81389
                                           uu____81391
                                          in
                                       giveup_or_defer env orig wl
                                         uu____81385)
                                    else first_order orig env wl lhs rhs1))
                      | uu____81403 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____81410 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____81410 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____81436 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____81436
                             | (FStar_Util.Inl msg,uu____81438) ->
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
                  (let uu____81483 =
                     let uu____81500 = quasi_pattern env lhs  in
                     let uu____81507 = quasi_pattern env rhs  in
                     (uu____81500, uu____81507)  in
                   match uu____81483 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____81550 = lhs  in
                       (match uu____81550 with
                        | ({ FStar_Syntax_Syntax.n = uu____81551;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____81553;_},u_lhs,uu____81555)
                            ->
                            let uu____81558 = rhs  in
                            (match uu____81558 with
                             | (uu____81559,u_rhs,uu____81561) ->
                                 let uu____81562 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____81562
                                 then
                                   let uu____81569 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____81569
                                 else
                                   (let uu____81572 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____81572 with
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
                                        let uu____81604 =
                                          let uu____81611 =
                                            let uu____81614 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____81614
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____81611
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____81604 with
                                         | (uu____81626,w,wl1) ->
                                             let w_app =
                                               let uu____81632 =
                                                 let uu____81637 =
                                                   FStar_List.map
                                                     (fun uu____81648  ->
                                                        match uu____81648
                                                        with
                                                        | (z,uu____81656) ->
                                                            let uu____81661 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____81661) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____81637
                                                  in
                                               uu____81632
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____81665 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____81665
                                               then
                                                 let uu____81670 =
                                                   let uu____81674 =
                                                     flex_t_to_string lhs  in
                                                   let uu____81676 =
                                                     let uu____81680 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____81682 =
                                                       let uu____81686 =
                                                         term_to_string w  in
                                                       let uu____81688 =
                                                         let uu____81692 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____81701 =
                                                           let uu____81705 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____81714 =
                                                             let uu____81718
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____81718]
                                                              in
                                                           uu____81705 ::
                                                             uu____81714
                                                            in
                                                         uu____81692 ::
                                                           uu____81701
                                                          in
                                                       uu____81686 ::
                                                         uu____81688
                                                        in
                                                     uu____81680 ::
                                                       uu____81682
                                                      in
                                                   uu____81674 :: uu____81676
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____81670
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____81735 =
                                                     let uu____81740 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____81740)  in
                                                   TERM uu____81735  in
                                                 let uu____81741 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____81741
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____81749 =
                                                        let uu____81754 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____81754)
                                                         in
                                                      TERM uu____81749  in
                                                    [s1; s2])
                                                  in
                                               let uu____81755 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____81755))))))
                   | uu____81756 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____81827 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____81827
            then
              let uu____81832 = FStar_Syntax_Print.term_to_string t1  in
              let uu____81834 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____81836 = FStar_Syntax_Print.term_to_string t2  in
              let uu____81838 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____81832 uu____81834 uu____81836 uu____81838
            else ());
           (let uu____81849 = FStar_Syntax_Util.head_and_args t1  in
            match uu____81849 with
            | (head1,args1) ->
                let uu____81892 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____81892 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____81962 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____81962 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____81992 =
                         let uu____81994 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____81996 = args_to_string args1  in
                         let uu____82000 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____82002 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____81994 uu____81996 uu____82000 uu____82002
                          in
                       giveup env1 uu____81992 orig
                     else
                       (let uu____82009 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____82018 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____82018 = FStar_Syntax_Util.Equal)
                           in
                        if uu____82009
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___3066_82022 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___3066_82022.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___3066_82022.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___3066_82022.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___3066_82022.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___3066_82022.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___3066_82022.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___3066_82022.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___3066_82022.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____82032 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____82032
                                    else solve env1 wl2))
                        else
                          (let uu____82037 = base_and_refinement env1 t1  in
                           match uu____82037 with
                           | (base1,refinement1) ->
                               let uu____82062 = base_and_refinement env1 t2
                                  in
                               (match uu____82062 with
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
                                           let uu____82227 =
                                             FStar_List.fold_right
                                               (fun uu____82267  ->
                                                  fun uu____82268  ->
                                                    match (uu____82267,
                                                            uu____82268)
                                                    with
                                                    | (((a1,uu____82320),
                                                        (a2,uu____82322)),
                                                       (probs,wl3)) ->
                                                        let uu____82371 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____82371
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____82227 with
                                           | (subprobs,wl3) ->
                                               ((let uu____82414 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82414
                                                 then
                                                   let uu____82419 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____82419
                                                 else ());
                                                (let uu____82425 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____82425
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
                                                    (let uu____82452 =
                                                       mk_sub_probs wl3  in
                                                     match uu____82452 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____82468 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____82468
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____82476 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____82476))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____82500 =
                                                    mk_sub_probs wl3  in
                                                  match uu____82500 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____82514 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____82514)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____82540 =
                                           match uu____82540 with
                                           | (prob,reason) ->
                                               ((let uu____82551 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____82551
                                                 then
                                                   let uu____82556 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____82558 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____82556 uu____82558
                                                     reason
                                                 else ());
                                                (let uu____82563 =
                                                   let uu____82572 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____82575 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____82572, uu____82575)
                                                    in
                                                 match uu____82563 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____82588 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____82588 with
                                                      | (head1',uu____82606)
                                                          ->
                                                          let uu____82631 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____82631
                                                           with
                                                           | (head2',uu____82649)
                                                               ->
                                                               let uu____82674
                                                                 =
                                                                 let uu____82679
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____82680
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____82679,
                                                                   uu____82680)
                                                                  in
                                                               (match uu____82674
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____82682
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82682
                                                                    then
                                                                    let uu____82687
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____82689
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____82691
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____82693
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____82687
                                                                    uu____82689
                                                                    uu____82691
                                                                    uu____82693
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____82698
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___3152_82706
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___3152_82706.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___3152_82706.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___3152_82706.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___3152_82706.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___3152_82706.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___3152_82706.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___3152_82706.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___3152_82706.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____82708
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____82708
                                                                    then
                                                                    let uu____82713
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____82713
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____82718 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____82730 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____82730 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____82738 =
                                             let uu____82739 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____82739.FStar_Syntax_Syntax.n
                                              in
                                           match uu____82738 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____82744 -> false  in
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
                                          | uu____82747 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____82750 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___3172_82786 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___3172_82786.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___3172_82786.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___3172_82786.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___3172_82786.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___3172_82786.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___3172_82786.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___3172_82786.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___3172_82786.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____82862 = destruct_flex_t scrutinee wl1  in
             match uu____82862 with
             | ((_t,uv,_args),wl2) ->
                 let uu____82873 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____82873 with
                  | (xs,pat_term,uu____82889,uu____82890) ->
                      let uu____82895 =
                        FStar_List.fold_left
                          (fun uu____82918  ->
                             fun x  ->
                               match uu____82918 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____82939 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____82939 with
                                    | (uu____82958,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____82895 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____82979 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____82979 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___3212_82996 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___3212_82996.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___3212_82996.umax_heuristic_ok);
                                    tcenv = (uu___3212_82996.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____83008 = solve env1 wl'  in
                                (match uu____83008 with
                                 | Success (uu____83011,imps) ->
                                     let wl'1 =
                                       let uu___3220_83014 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___3220_83014.wl_deferred);
                                         ctr = (uu___3220_83014.ctr);
                                         defer_ok =
                                           (uu___3220_83014.defer_ok);
                                         smt_ok = (uu___3220_83014.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___3220_83014.umax_heuristic_ok);
                                         tcenv = (uu___3220_83014.tcenv);
                                         wl_implicits =
                                           (uu___3220_83014.wl_implicits)
                                       }  in
                                     let uu____83015 = solve env1 wl'1  in
                                     (match uu____83015 with
                                      | Success (uu____83018,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___3228_83022 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___3228_83022.attempting);
                                                 wl_deferred =
                                                   (uu___3228_83022.wl_deferred);
                                                 ctr = (uu___3228_83022.ctr);
                                                 defer_ok =
                                                   (uu___3228_83022.defer_ok);
                                                 smt_ok =
                                                   (uu___3228_83022.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3228_83022.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3228_83022.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____83023 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____83030 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____83053 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____83053
                 then
                   let uu____83058 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____83060 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____83058 uu____83060
                 else ());
                (let uu____83065 =
                   let uu____83086 =
                     let uu____83095 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____83095)  in
                   let uu____83102 =
                     let uu____83111 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____83111)  in
                   (uu____83086, uu____83102)  in
                 match uu____83065 with
                 | ((uu____83141,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____83144;
                                   FStar_Syntax_Syntax.vars = uu____83145;_}),
                    (s,t)) ->
                     let uu____83216 =
                       let uu____83218 = is_flex scrutinee  in
                       Prims.op_Negation uu____83218  in
                     if uu____83216
                     then
                       ((let uu____83229 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____83229
                         then
                           let uu____83234 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____83234
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____83253 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83253
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____83268 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____83268
                           then
                             let uu____83273 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____83275 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____83273 uu____83275
                           else ());
                          (let pat_discriminates uu___613_83300 =
                             match uu___613_83300 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____83316;
                                  FStar_Syntax_Syntax.p = uu____83317;_},FStar_Pervasives_Native.None
                                ,uu____83318) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____83332;
                                  FStar_Syntax_Syntax.p = uu____83333;_},FStar_Pervasives_Native.None
                                ,uu____83334) -> true
                             | uu____83361 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____83464 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____83464 with
                                       | (uu____83466,uu____83467,t') ->
                                           let uu____83485 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____83485 with
                                            | (FullMatch ,uu____83497) ->
                                                true
                                            | (HeadMatch
                                               uu____83511,uu____83512) ->
                                                true
                                            | uu____83527 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____83564 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____83564
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____83575 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____83575 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____83663,uu____83664) ->
                                       branches1
                                   | uu____83809 -> branches  in
                                 let uu____83864 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____83873 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____83873 with
                                        | (p,uu____83877,uu____83878) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _83907  -> FStar_Util.Inr _83907)
                                   uu____83864))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____83937 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____83937 with
                                | (p,uu____83946,e) ->
                                    ((let uu____83965 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____83965
                                      then
                                        let uu____83970 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____83972 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____83970 uu____83972
                                      else ());
                                     (let uu____83977 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _83992  -> FStar_Util.Inr _83992)
                                        uu____83977)))))
                 | ((s,t),(uu____83995,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____83998;
                                         FStar_Syntax_Syntax.vars =
                                           uu____83999;_}))
                     ->
                     let uu____84068 =
                       let uu____84070 = is_flex scrutinee  in
                       Prims.op_Negation uu____84070  in
                     if uu____84068
                     then
                       ((let uu____84081 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____84081
                         then
                           let uu____84086 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____84086
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____84105 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84105
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____84120 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____84120
                           then
                             let uu____84125 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____84127 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____84125 uu____84127
                           else ());
                          (let pat_discriminates uu___613_84152 =
                             match uu___613_84152 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____84168;
                                  FStar_Syntax_Syntax.p = uu____84169;_},FStar_Pervasives_Native.None
                                ,uu____84170) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____84184;
                                  FStar_Syntax_Syntax.p = uu____84185;_},FStar_Pervasives_Native.None
                                ,uu____84186) -> true
                             | uu____84213 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____84316 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____84316 with
                                       | (uu____84318,uu____84319,t') ->
                                           let uu____84337 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____84337 with
                                            | (FullMatch ,uu____84349) ->
                                                true
                                            | (HeadMatch
                                               uu____84363,uu____84364) ->
                                                true
                                            | uu____84379 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____84416 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____84416
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____84427 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____84427 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____84515,uu____84516) ->
                                       branches1
                                   | uu____84661 -> branches  in
                                 let uu____84716 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____84725 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____84725 with
                                        | (p,uu____84729,uu____84730) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _84759  -> FStar_Util.Inr _84759)
                                   uu____84716))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____84789 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____84789 with
                                | (p,uu____84798,e) ->
                                    ((let uu____84817 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____84817
                                      then
                                        let uu____84822 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____84824 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____84822 uu____84824
                                      else ());
                                     (let uu____84829 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _84844  -> FStar_Util.Inr _84844)
                                        uu____84829)))))
                 | uu____84845 ->
                     ((let uu____84867 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____84867
                       then
                         let uu____84872 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____84874 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____84872 uu____84874
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____84920 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____84920
            then
              let uu____84925 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____84927 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____84929 = FStar_Syntax_Print.term_to_string t1  in
              let uu____84931 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____84925 uu____84927 uu____84929 uu____84931
            else ());
           (let uu____84936 = head_matches_delta env1 wl1 t1 t2  in
            match uu____84936 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____84967,uu____84968) ->
                     let rec may_relate head3 =
                       let uu____84996 =
                         let uu____84997 = FStar_Syntax_Subst.compress head3
                            in
                         uu____84997.FStar_Syntax_Syntax.n  in
                       match uu____84996 with
                       | FStar_Syntax_Syntax.Tm_name uu____85001 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____85003 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____85028 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____85028 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____85030 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____85033
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____85034 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____85037,uu____85038) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____85080) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____85086) ->
                           may_relate t
                       | uu____85091 -> false  in
                     let uu____85093 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____85093 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____85114 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____85114
                          then
                            let uu____85117 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____85117 with
                             | (guard,wl2) ->
                                 let uu____85124 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____85124)
                          else
                            (let uu____85127 =
                               let uu____85129 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____85131 =
                                 let uu____85133 =
                                   let uu____85137 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____85137
                                     (fun x  ->
                                        let uu____85144 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85144)
                                    in
                                 FStar_Util.dflt "" uu____85133  in
                               let uu____85149 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____85151 =
                                 let uu____85153 =
                                   let uu____85157 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____85157
                                     (fun x  ->
                                        let uu____85164 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____85164)
                                    in
                                 FStar_Util.dflt "" uu____85153  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____85129 uu____85131 uu____85149
                                 uu____85151
                                in
                             giveup env1 uu____85127 orig))
                 | (HeadMatch (true ),uu____85170) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____85185 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____85185 with
                        | (guard,wl2) ->
                            let uu____85192 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____85192)
                     else
                       (let uu____85195 =
                          let uu____85197 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____85199 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____85197 uu____85199
                           in
                        giveup env1 uu____85195 orig)
                 | (uu____85202,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___3401_85216 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___3401_85216.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___3401_85216.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___3401_85216.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___3401_85216.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___3401_85216.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___3401_85216.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___3401_85216.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___3401_85216.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____85243 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____85243
          then
            let uu____85246 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____85246
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____85252 =
                let uu____85255 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85255  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____85252 t1);
             (let uu____85274 =
                let uu____85277 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____85277  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____85274 t2);
             (let uu____85296 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____85296
              then
                let uu____85300 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____85302 =
                  let uu____85304 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____85306 =
                    let uu____85308 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____85308  in
                  Prims.op_Hat uu____85304 uu____85306  in
                let uu____85311 =
                  let uu____85313 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____85315 =
                    let uu____85317 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____85317  in
                  Prims.op_Hat uu____85313 uu____85315  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____85300 uu____85302 uu____85311
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____85324,uu____85325) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____85349,FStar_Syntax_Syntax.Tm_delayed uu____85350) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____85374,uu____85375) ->
                  let uu____85402 =
                    let uu___3432_85403 = problem  in
                    let uu____85404 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3432_85403.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85404;
                      FStar_TypeChecker_Common.relation =
                        (uu___3432_85403.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3432_85403.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3432_85403.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3432_85403.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3432_85403.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3432_85403.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3432_85403.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3432_85403.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85402 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____85405,uu____85406) ->
                  let uu____85413 =
                    let uu___3438_85414 = problem  in
                    let uu____85415 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3438_85414.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____85415;
                      FStar_TypeChecker_Common.relation =
                        (uu___3438_85414.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3438_85414.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3438_85414.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3438_85414.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3438_85414.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3438_85414.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3438_85414.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3438_85414.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85413 wl
              | (uu____85416,FStar_Syntax_Syntax.Tm_ascribed uu____85417) ->
                  let uu____85444 =
                    let uu___3444_85445 = problem  in
                    let uu____85446 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3444_85445.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3444_85445.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3444_85445.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85446;
                      FStar_TypeChecker_Common.element =
                        (uu___3444_85445.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3444_85445.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3444_85445.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3444_85445.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3444_85445.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3444_85445.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85444 wl
              | (uu____85447,FStar_Syntax_Syntax.Tm_meta uu____85448) ->
                  let uu____85455 =
                    let uu___3450_85456 = problem  in
                    let uu____85457 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3450_85456.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3450_85456.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3450_85456.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____85457;
                      FStar_TypeChecker_Common.element =
                        (uu___3450_85456.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3450_85456.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3450_85456.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3450_85456.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3450_85456.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3450_85456.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____85455 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____85459),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____85461)) ->
                  let uu____85470 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____85470
              | (FStar_Syntax_Syntax.Tm_bvar uu____85471,uu____85472) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____85474,FStar_Syntax_Syntax.Tm_bvar uu____85475) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___614_85545 =
                    match uu___614_85545 with
                    | [] -> c
                    | bs ->
                        let uu____85573 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____85573
                     in
                  let uu____85584 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____85584 with
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
                                    let uu____85733 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____85733
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
                  let mk_t t l uu___615_85822 =
                    match uu___615_85822 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____85864 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____85864 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____86009 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____86010 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____86009
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____86010 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____86012,uu____86013) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86044 -> true
                    | uu____86064 -> false  in
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
                      (let uu____86124 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86132 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86132.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86132.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86132.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86132.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86132.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86132.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86132.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86132.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86132.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86132.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86132.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86132.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86132.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86132.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86132.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86132.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86132.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86132.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86132.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86132.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86132.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86132.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86132.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86132.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86132.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86132.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86132.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86132.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86132.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86132.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86132.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86132.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86132.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86132.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86132.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86132.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86132.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86132.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86132.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86132.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86124 with
                       | (uu____86137,ty,uu____86139) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86148 =
                                 let uu____86149 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86149.FStar_Syntax_Syntax.n  in
                               match uu____86148 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86152 ->
                                   let uu____86159 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86159
                               | uu____86160 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86163 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86163
                             then
                               let uu____86168 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86170 =
                                 let uu____86172 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86172
                                  in
                               let uu____86173 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86168 uu____86170 uu____86173
                             else ());
                            r1))
                     in
                  let uu____86178 =
                    let uu____86195 = maybe_eta t1  in
                    let uu____86202 = maybe_eta t2  in
                    (uu____86195, uu____86202)  in
                  (match uu____86178 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86244 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86244.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86244.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86244.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86244.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86244.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86244.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86244.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86244.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86265 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86265
                       then
                         let uu____86268 = destruct_flex_t not_abs wl  in
                         (match uu____86268 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86285 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86285.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86285.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86285.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86285.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86285.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86285.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86285.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86285.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86309 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86309
                       then
                         let uu____86312 = destruct_flex_t not_abs wl  in
                         (match uu____86312 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86329 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86329.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86329.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86329.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86329.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86329.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86329.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86329.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86329.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86333 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____86351,FStar_Syntax_Syntax.Tm_abs uu____86352) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____86383 -> true
                    | uu____86403 -> false  in
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
                      (let uu____86463 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3552_86471 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3552_86471.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3552_86471.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3552_86471.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3552_86471.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3552_86471.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3552_86471.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3552_86471.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3552_86471.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3552_86471.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___3552_86471.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3552_86471.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3552_86471.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3552_86471.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3552_86471.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3552_86471.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3552_86471.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3552_86471.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3552_86471.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3552_86471.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3552_86471.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3552_86471.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3552_86471.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3552_86471.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3552_86471.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3552_86471.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3552_86471.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3552_86471.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3552_86471.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3552_86471.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3552_86471.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3552_86471.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3552_86471.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3552_86471.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3552_86471.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3552_86471.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3552_86471.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3552_86471.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3552_86471.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3552_86471.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3552_86471.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____86463 with
                       | (uu____86476,ty,uu____86478) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____86487 =
                                 let uu____86488 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____86488.FStar_Syntax_Syntax.n  in
                               match uu____86487 with
                               | FStar_Syntax_Syntax.Tm_refine uu____86491 ->
                                   let uu____86498 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____86498
                               | uu____86499 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____86502 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____86502
                             then
                               let uu____86507 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____86509 =
                                 let uu____86511 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____86511
                                  in
                               let uu____86512 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____86507 uu____86509 uu____86512
                             else ());
                            r1))
                     in
                  let uu____86517 =
                    let uu____86534 = maybe_eta t1  in
                    let uu____86541 = maybe_eta t2  in
                    (uu____86534, uu____86541)  in
                  (match uu____86517 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3573_86583 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3573_86583.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3573_86583.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3573_86583.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3573_86583.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3573_86583.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3573_86583.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3573_86583.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3573_86583.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____86604 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86604
                       then
                         let uu____86607 = destruct_flex_t not_abs wl  in
                         (match uu____86607 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86624 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86624.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86624.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86624.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86624.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86624.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86624.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86624.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86624.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____86648 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____86648
                       then
                         let uu____86651 = destruct_flex_t not_abs wl  in
                         (match uu____86651 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3590_86668 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3590_86668.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3590_86668.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3590_86668.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3590_86668.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3590_86668.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3590_86668.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3590_86668.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3590_86668.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____86672 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____86702 =
                    let uu____86707 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____86707 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3613_86735 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86735.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86735.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86737 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86737.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86737.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____86738,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3613_86753 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3613_86753.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3613_86753.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3615_86755 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3615_86755.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3615_86755.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____86756 -> (x1, x2)  in
                  (match uu____86702 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____86775 = as_refinement false env t11  in
                       (match uu____86775 with
                        | (x12,phi11) ->
                            let uu____86783 = as_refinement false env t21  in
                            (match uu____86783 with
                             | (x22,phi21) ->
                                 ((let uu____86792 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____86792
                                   then
                                     ((let uu____86797 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____86799 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86801 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____86797
                                         uu____86799 uu____86801);
                                      (let uu____86804 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____86806 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____86808 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____86804
                                         uu____86806 uu____86808))
                                   else ());
                                  (let uu____86813 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____86813 with
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
                                         let uu____86884 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____86884
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____86896 =
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
                                         (let uu____86909 =
                                            let uu____86912 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____86912
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____86909
                                            (p_guard base_prob));
                                         (let uu____86931 =
                                            let uu____86934 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____86934
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____86931
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____86953 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____86953)
                                          in
                                       let has_uvars =
                                         (let uu____86958 =
                                            let uu____86960 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____86960
                                             in
                                          Prims.op_Negation uu____86958) ||
                                           (let uu____86964 =
                                              let uu____86966 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____86966
                                               in
                                            Prims.op_Negation uu____86964)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____86970 =
                                           let uu____86975 =
                                             let uu____86984 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____86984]  in
                                           mk_t_problem wl1 uu____86975 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____86970 with
                                          | (ref_prob,wl2) ->
                                              let uu____87006 =
                                                solve env1
                                                  (let uu___3657_87008 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3657_87008.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3657_87008.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3657_87008.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3657_87008.tcenv);
                                                     wl_implicits =
                                                       (uu___3657_87008.wl_implicits)
                                                   })
                                                 in
                                              (match uu____87006 with
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
                                               | Success uu____87025 ->
                                                   let guard =
                                                     let uu____87033 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____87033
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3668_87042 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3668_87042.attempting);
                                                       wl_deferred =
                                                         (uu___3668_87042.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___3668_87042.defer_ok);
                                                       smt_ok =
                                                         (uu___3668_87042.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3668_87042.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3668_87042.tcenv);
                                                       wl_implicits =
                                                         (uu___3668_87042.wl_implicits)
                                                     }  in
                                                   let uu____87044 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____87044))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87047,FStar_Syntax_Syntax.Tm_uvar uu____87048) ->
                  let uu____87073 = destruct_flex_t t1 wl  in
                  (match uu____87073 with
                   | (f1,wl1) ->
                       let uu____87080 = destruct_flex_t t2 wl1  in
                       (match uu____87080 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87087;
                    FStar_Syntax_Syntax.pos = uu____87088;
                    FStar_Syntax_Syntax.vars = uu____87089;_},uu____87090),FStar_Syntax_Syntax.Tm_uvar
                 uu____87091) ->
                  let uu____87140 = destruct_flex_t t1 wl  in
                  (match uu____87140 with
                   | (f1,wl1) ->
                       let uu____87147 = destruct_flex_t t2 wl1  in
                       (match uu____87147 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87154,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87155;
                    FStar_Syntax_Syntax.pos = uu____87156;
                    FStar_Syntax_Syntax.vars = uu____87157;_},uu____87158))
                  ->
                  let uu____87207 = destruct_flex_t t1 wl  in
                  (match uu____87207 with
                   | (f1,wl1) ->
                       let uu____87214 = destruct_flex_t t2 wl1  in
                       (match uu____87214 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87221;
                    FStar_Syntax_Syntax.pos = uu____87222;
                    FStar_Syntax_Syntax.vars = uu____87223;_},uu____87224),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87225;
                    FStar_Syntax_Syntax.pos = uu____87226;
                    FStar_Syntax_Syntax.vars = uu____87227;_},uu____87228))
                  ->
                  let uu____87301 = destruct_flex_t t1 wl  in
                  (match uu____87301 with
                   | (f1,wl1) ->
                       let uu____87308 = destruct_flex_t t2 wl1  in
                       (match uu____87308 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____87315,uu____87316) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87329 = destruct_flex_t t1 wl  in
                  (match uu____87329 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87336;
                    FStar_Syntax_Syntax.pos = uu____87337;
                    FStar_Syntax_Syntax.vars = uu____87338;_},uu____87339),uu____87340)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____87377 = destruct_flex_t t1 wl  in
                  (match uu____87377 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____87384,FStar_Syntax_Syntax.Tm_uvar uu____87385) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____87398,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87399;
                    FStar_Syntax_Syntax.pos = uu____87400;
                    FStar_Syntax_Syntax.vars = uu____87401;_},uu____87402))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____87439,FStar_Syntax_Syntax.Tm_arrow uu____87440) ->
                  solve_t' env
                    (let uu___3768_87468 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87468.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87468.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87468.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87468.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87468.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87468.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87468.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87468.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87468.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87469;
                    FStar_Syntax_Syntax.pos = uu____87470;
                    FStar_Syntax_Syntax.vars = uu____87471;_},uu____87472),FStar_Syntax_Syntax.Tm_arrow
                 uu____87473) ->
                  solve_t' env
                    (let uu___3768_87525 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3768_87525.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3768_87525.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3768_87525.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3768_87525.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3768_87525.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3768_87525.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3768_87525.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3768_87525.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3768_87525.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87526,FStar_Syntax_Syntax.Tm_uvar uu____87527) ->
                  let uu____87540 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87540
              | (uu____87541,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87542;
                    FStar_Syntax_Syntax.pos = uu____87543;
                    FStar_Syntax_Syntax.vars = uu____87544;_},uu____87545))
                  ->
                  let uu____87582 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87582
              | (FStar_Syntax_Syntax.Tm_uvar uu____87583,uu____87584) ->
                  let uu____87597 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87597
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____87598;
                    FStar_Syntax_Syntax.pos = uu____87599;
                    FStar_Syntax_Syntax.vars = uu____87600;_},uu____87601),uu____87602)
                  ->
                  let uu____87639 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____87639
              | (FStar_Syntax_Syntax.Tm_refine uu____87640,uu____87641) ->
                  let t21 =
                    let uu____87649 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____87649  in
                  solve_t env
                    (let uu___3803_87675 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3803_87675.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3803_87675.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3803_87675.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3803_87675.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3803_87675.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3803_87675.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3803_87675.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3803_87675.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3803_87675.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____87676,FStar_Syntax_Syntax.Tm_refine uu____87677) ->
                  let t11 =
                    let uu____87685 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____87685  in
                  solve_t env
                    (let uu___3810_87711 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3810_87711.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3810_87711.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3810_87711.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3810_87711.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3810_87711.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3810_87711.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3810_87711.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3810_87711.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3810_87711.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____87793 =
                    let uu____87794 = guard_of_prob env wl problem t1 t2  in
                    match uu____87794 with
                    | (guard,wl1) ->
                        let uu____87801 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____87801
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____88020 = br1  in
                        (match uu____88020 with
                         | (p1,w1,uu____88049) ->
                             let uu____88066 = br2  in
                             (match uu____88066 with
                              | (p2,w2,uu____88089) ->
                                  let uu____88094 =
                                    let uu____88096 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____88096  in
                                  if uu____88094
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____88123 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____88123 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____88160 = br2  in
                                         (match uu____88160 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____88193 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____88193
                                                 in
                                              let uu____88198 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____88229,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____88250) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____88309 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____88309 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____88198
                                                (fun uu____88381  ->
                                                   match uu____88381 with
                                                   | (wprobs,wl2) ->
                                                       let uu____88418 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____88418
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____88439
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____88439
                                                              then
                                                                let uu____88444
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____88446
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____88444
                                                                  uu____88446
                                                              else ());
                                                             (let uu____88452
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____88452
                                                                (fun
                                                                   uu____88488
                                                                    ->
                                                                   match uu____88488
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
                    | uu____88617 -> FStar_Pervasives_Native.None  in
                  let uu____88658 = solve_branches wl brs1 brs2  in
                  (match uu____88658 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____88709 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____88709 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____88743 =
                                FStar_List.map
                                  (fun uu____88755  ->
                                     match uu____88755 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____88743  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____88764 =
                              let uu____88765 =
                                let uu____88766 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____88766
                                  (let uu___3909_88774 = wl3  in
                                   {
                                     attempting =
                                       (uu___3909_88774.attempting);
                                     wl_deferred =
                                       (uu___3909_88774.wl_deferred);
                                     ctr = (uu___3909_88774.ctr);
                                     defer_ok = (uu___3909_88774.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3909_88774.umax_heuristic_ok);
                                     tcenv = (uu___3909_88774.tcenv);
                                     wl_implicits =
                                       (uu___3909_88774.wl_implicits)
                                   })
                                 in
                              solve env uu____88765  in
                            (match uu____88764 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____88779 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____88786,uu____88787) ->
                  let head1 =
                    let uu____88811 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____88811
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____88857 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____88857
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____88903 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____88903
                    then
                      let uu____88907 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____88909 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____88911 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____88907 uu____88909 uu____88911
                    else ());
                   (let no_free_uvars t =
                      (let uu____88925 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____88925) &&
                        (let uu____88929 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____88929)
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
                      let uu____88946 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____88946 = FStar_Syntax_Util.Equal  in
                    let uu____88947 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____88947
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____88951 = equal t1 t2  in
                         (if uu____88951
                          then
                            let uu____88954 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____88954
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____88959 =
                            let uu____88966 = equal t1 t2  in
                            if uu____88966
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____88979 = mk_eq2 wl env orig t1 t2  in
                               match uu____88979 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____88959 with
                          | (guard,wl1) ->
                              let uu____89000 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89000))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____89003,uu____89004) ->
                  let head1 =
                    let uu____89012 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89012
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89058 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89058
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89104 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89104
                    then
                      let uu____89108 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89110 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89112 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89108 uu____89110 uu____89112
                    else ());
                   (let no_free_uvars t =
                      (let uu____89126 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89126) &&
                        (let uu____89130 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89130)
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
                      let uu____89147 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89147 = FStar_Syntax_Util.Equal  in
                    let uu____89148 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89148
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89152 = equal t1 t2  in
                         (if uu____89152
                          then
                            let uu____89155 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89155
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89160 =
                            let uu____89167 = equal t1 t2  in
                            if uu____89167
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89180 = mk_eq2 wl env orig t1 t2  in
                               match uu____89180 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89160 with
                          | (guard,wl1) ->
                              let uu____89201 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89201))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____89204,uu____89205) ->
                  let head1 =
                    let uu____89207 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89207
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89253 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89253
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89299 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89299
                    then
                      let uu____89303 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89305 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89307 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89303 uu____89305 uu____89307
                    else ());
                   (let no_free_uvars t =
                      (let uu____89321 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89321) &&
                        (let uu____89325 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89325)
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
                      let uu____89342 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89342 = FStar_Syntax_Util.Equal  in
                    let uu____89343 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89343
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89347 = equal t1 t2  in
                         (if uu____89347
                          then
                            let uu____89350 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89350
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89355 =
                            let uu____89362 = equal t1 t2  in
                            if uu____89362
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89375 = mk_eq2 wl env orig t1 t2  in
                               match uu____89375 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89355 with
                          | (guard,wl1) ->
                              let uu____89396 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89396))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____89399,uu____89400) ->
                  let head1 =
                    let uu____89402 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89402
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89448 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89448
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89494 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89494
                    then
                      let uu____89498 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89500 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89502 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89498 uu____89500 uu____89502
                    else ());
                   (let no_free_uvars t =
                      (let uu____89516 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89516) &&
                        (let uu____89520 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89520)
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
                      let uu____89537 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89537 = FStar_Syntax_Util.Equal  in
                    let uu____89538 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89538
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89542 = equal t1 t2  in
                         (if uu____89542
                          then
                            let uu____89545 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89545
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89550 =
                            let uu____89557 = equal t1 t2  in
                            if uu____89557
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89570 = mk_eq2 wl env orig t1 t2  in
                               match uu____89570 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89550 with
                          | (guard,wl1) ->
                              let uu____89591 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89591))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____89594,uu____89595) ->
                  let head1 =
                    let uu____89597 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89597
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89643 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89643
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89689 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89689
                    then
                      let uu____89693 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89695 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89697 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89693 uu____89695 uu____89697
                    else ());
                   (let no_free_uvars t =
                      (let uu____89711 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89711) &&
                        (let uu____89715 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89715)
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
                      let uu____89732 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89732 = FStar_Syntax_Util.Equal  in
                    let uu____89733 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89733
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89737 = equal t1 t2  in
                         (if uu____89737
                          then
                            let uu____89740 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89740
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89745 =
                            let uu____89752 = equal t1 t2  in
                            if uu____89752
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89765 = mk_eq2 wl env orig t1 t2  in
                               match uu____89765 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89745 with
                          | (guard,wl1) ->
                              let uu____89786 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89786))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____89789,uu____89790) ->
                  let head1 =
                    let uu____89808 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____89808
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____89854 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____89854
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____89900 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____89900
                    then
                      let uu____89904 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____89906 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____89908 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____89904 uu____89906 uu____89908
                    else ());
                   (let no_free_uvars t =
                      (let uu____89922 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____89922) &&
                        (let uu____89926 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____89926)
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
                      let uu____89943 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____89943 = FStar_Syntax_Util.Equal  in
                    let uu____89944 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____89944
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____89948 = equal t1 t2  in
                         (if uu____89948
                          then
                            let uu____89951 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____89951
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____89956 =
                            let uu____89963 = equal t1 t2  in
                            if uu____89963
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____89976 = mk_eq2 wl env orig t1 t2  in
                               match uu____89976 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____89956 with
                          | (guard,wl1) ->
                              let uu____89997 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____89997))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90000,FStar_Syntax_Syntax.Tm_match uu____90001) ->
                  let head1 =
                    let uu____90025 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90025
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90071 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90071
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90117 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90117
                    then
                      let uu____90121 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90123 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90125 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90121 uu____90123 uu____90125
                    else ());
                   (let no_free_uvars t =
                      (let uu____90139 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90139) &&
                        (let uu____90143 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90143)
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
                      let uu____90160 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90160 = FStar_Syntax_Util.Equal  in
                    let uu____90161 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90161
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90165 = equal t1 t2  in
                         (if uu____90165
                          then
                            let uu____90168 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90168
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90173 =
                            let uu____90180 = equal t1 t2  in
                            if uu____90180
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90193 = mk_eq2 wl env orig t1 t2  in
                               match uu____90193 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90173 with
                          | (guard,wl1) ->
                              let uu____90214 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90214))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90217,FStar_Syntax_Syntax.Tm_uinst uu____90218) ->
                  let head1 =
                    let uu____90226 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90226
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90266 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90266
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90306 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90306
                    then
                      let uu____90310 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90312 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90314 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90310 uu____90312 uu____90314
                    else ());
                   (let no_free_uvars t =
                      (let uu____90328 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90328) &&
                        (let uu____90332 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90332)
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
                      let uu____90349 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90349 = FStar_Syntax_Util.Equal  in
                    let uu____90350 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90350
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90354 = equal t1 t2  in
                         (if uu____90354
                          then
                            let uu____90357 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90357
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90362 =
                            let uu____90369 = equal t1 t2  in
                            if uu____90369
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90382 = mk_eq2 wl env orig t1 t2  in
                               match uu____90382 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90362 with
                          | (guard,wl1) ->
                              let uu____90403 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90403))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90406,FStar_Syntax_Syntax.Tm_name uu____90407) ->
                  let head1 =
                    let uu____90409 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90409
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90449 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90449
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90489 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90489
                    then
                      let uu____90493 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90495 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90497 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90493 uu____90495 uu____90497
                    else ());
                   (let no_free_uvars t =
                      (let uu____90511 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90511) &&
                        (let uu____90515 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90515)
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
                      let uu____90532 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90532 = FStar_Syntax_Util.Equal  in
                    let uu____90533 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90533
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90537 = equal t1 t2  in
                         (if uu____90537
                          then
                            let uu____90540 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90540
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90545 =
                            let uu____90552 = equal t1 t2  in
                            if uu____90552
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90565 = mk_eq2 wl env orig t1 t2  in
                               match uu____90565 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90545 with
                          | (guard,wl1) ->
                              let uu____90586 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90586))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90589,FStar_Syntax_Syntax.Tm_constant uu____90590) ->
                  let head1 =
                    let uu____90592 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90592
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90632 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90632
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90672 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90672
                    then
                      let uu____90676 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90678 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90680 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90676 uu____90678 uu____90680
                    else ());
                   (let no_free_uvars t =
                      (let uu____90694 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90694) &&
                        (let uu____90698 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90698)
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
                      let uu____90715 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90715 = FStar_Syntax_Util.Equal  in
                    let uu____90716 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90716
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90720 = equal t1 t2  in
                         (if uu____90720
                          then
                            let uu____90723 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90723
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90728 =
                            let uu____90735 = equal t1 t2  in
                            if uu____90735
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90748 = mk_eq2 wl env orig t1 t2  in
                               match uu____90748 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90728 with
                          | (guard,wl1) ->
                              let uu____90769 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90769))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90772,FStar_Syntax_Syntax.Tm_fvar uu____90773) ->
                  let head1 =
                    let uu____90775 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90775
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____90815 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____90815
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____90855 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____90855
                    then
                      let uu____90859 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____90861 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____90863 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____90859 uu____90861 uu____90863
                    else ());
                   (let no_free_uvars t =
                      (let uu____90877 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____90877) &&
                        (let uu____90881 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____90881)
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
                      let uu____90898 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____90898 = FStar_Syntax_Util.Equal  in
                    let uu____90899 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____90899
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____90903 = equal t1 t2  in
                         (if uu____90903
                          then
                            let uu____90906 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____90906
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____90911 =
                            let uu____90918 = equal t1 t2  in
                            if uu____90918
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____90931 = mk_eq2 wl env orig t1 t2  in
                               match uu____90931 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____90911 with
                          | (guard,wl1) ->
                              let uu____90952 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____90952))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____90955,FStar_Syntax_Syntax.Tm_app uu____90956) ->
                  let head1 =
                    let uu____90974 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____90974
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____91014 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____91014
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____91054 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____91054
                    then
                      let uu____91058 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____91060 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____91062 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____91058 uu____91060 uu____91062
                    else ());
                   (let no_free_uvars t =
                      (let uu____91076 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____91076) &&
                        (let uu____91080 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____91080)
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
                      let uu____91097 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____91097 = FStar_Syntax_Util.Equal  in
                    let uu____91098 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____91098
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____91102 = equal t1 t2  in
                         (if uu____91102
                          then
                            let uu____91105 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____91105
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____91110 =
                            let uu____91117 = equal t1 t2  in
                            if uu____91117
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____91130 = mk_eq2 wl env orig t1 t2  in
                               match uu____91130 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____91110 with
                          | (guard,wl1) ->
                              let uu____91151 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____91151))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____91154,FStar_Syntax_Syntax.Tm_let uu____91155) ->
                  let uu____91182 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____91182
                  then
                    let uu____91185 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____91185
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____91189,uu____91190) ->
                  let uu____91204 =
                    let uu____91210 =
                      let uu____91212 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91214 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91216 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91218 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91212 uu____91214 uu____91216 uu____91218
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91210)
                     in
                  FStar_Errors.raise_error uu____91204
                    t1.FStar_Syntax_Syntax.pos
              | (uu____91222,FStar_Syntax_Syntax.Tm_let uu____91223) ->
                  let uu____91237 =
                    let uu____91243 =
                      let uu____91245 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____91247 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____91249 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____91251 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____91245 uu____91247 uu____91249 uu____91251
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____91243)
                     in
                  FStar_Errors.raise_error uu____91237
                    t1.FStar_Syntax_Syntax.pos
              | uu____91255 -> giveup env "head tag mismatch" orig))))

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
          (let uu____91319 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____91319
           then
             let uu____91324 =
               let uu____91326 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____91326  in
             let uu____91327 =
               let uu____91329 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____91329  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____91324 uu____91327
           else ());
          (let uu____91333 =
             let uu____91335 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____91335  in
           if uu____91333
           then
             let uu____91338 =
               let uu____91340 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____91342 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____91340 uu____91342
                in
             giveup env uu____91338 orig
           else
             (let uu____91347 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____91347 with
              | (ret_sub_prob,wl1) ->
                  let uu____91355 =
                    FStar_List.fold_right2
                      (fun uu____91392  ->
                         fun uu____91393  ->
                           fun uu____91394  ->
                             match (uu____91392, uu____91393, uu____91394)
                             with
                             | ((a1,uu____91438),(a2,uu____91440),(arg_sub_probs,wl2))
                                 ->
                                 let uu____91473 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____91473 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____91355 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____91503 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____91503  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____91511 = attempt sub_probs wl3  in
                       solve env uu____91511)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____91534 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____91537)::[] -> wp1
              | uu____91562 ->
                  let uu____91573 =
                    let uu____91575 =
                      let uu____91577 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____91577  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____91575
                     in
                  failwith uu____91573
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____91584 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____91584]
              | x -> x  in
            let uu____91586 =
              let uu____91597 =
                let uu____91606 =
                  let uu____91607 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____91607 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____91606  in
              [uu____91597]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____91586;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____91625 = lift_c1 ()  in solve_eq uu____91625 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___616_91634  ->
                       match uu___616_91634 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____91639 -> false))
                in
             let uu____91641 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____91671)::uu____91672,(wp2,uu____91674)::uu____91675)
                   -> (wp1, wp2)
               | uu____91748 ->
                   let uu____91773 =
                     let uu____91779 =
                       let uu____91781 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____91783 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____91781 uu____91783
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____91779)
                      in
                   FStar_Errors.raise_error uu____91773
                     env.FStar_TypeChecker_Env.range
                in
             match uu____91641 with
             | (wpc1,wpc2) ->
                 let uu____91793 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____91793
                 then
                   let uu____91798 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____91798 wl
                 else
                   (let uu____91802 =
                      let uu____91809 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____91809  in
                    match uu____91802 with
                    | (c2_decl,qualifiers) ->
                        let uu____91830 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____91830
                        then
                          let c1_repr =
                            let uu____91837 =
                              let uu____91838 =
                                let uu____91839 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____91839  in
                              let uu____91840 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91838 uu____91840
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91837
                             in
                          let c2_repr =
                            let uu____91842 =
                              let uu____91843 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____91844 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____91843 uu____91844
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____91842
                             in
                          let uu____91845 =
                            let uu____91850 =
                              let uu____91852 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____91854 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____91852 uu____91854
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____91850
                             in
                          (match uu____91845 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____91860 = attempt [prob] wl2  in
                               solve env uu____91860)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____91875 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____91875
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____91884 =
                                     let uu____91891 =
                                       let uu____91892 =
                                         let uu____91909 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____91912 =
                                           let uu____91923 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____91932 =
                                             let uu____91943 =
                                               let uu____91952 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____91952
                                                in
                                             [uu____91943]  in
                                           uu____91923 :: uu____91932  in
                                         (uu____91909, uu____91912)  in
                                       FStar_Syntax_Syntax.Tm_app uu____91892
                                        in
                                     FStar_Syntax_Syntax.mk uu____91891  in
                                   uu____91884 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____92004 =
                                    let uu____92011 =
                                      let uu____92012 =
                                        let uu____92029 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____92032 =
                                          let uu____92043 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____92052 =
                                            let uu____92063 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____92072 =
                                              let uu____92083 =
                                                let uu____92092 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____92092
                                                 in
                                              [uu____92083]  in
                                            uu____92063 :: uu____92072  in
                                          uu____92043 :: uu____92052  in
                                        (uu____92029, uu____92032)  in
                                      FStar_Syntax_Syntax.Tm_app uu____92012
                                       in
                                    FStar_Syntax_Syntax.mk uu____92011  in
                                  uu____92004 FStar_Pervasives_Native.None r)
                              in
                           (let uu____92149 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92149
                            then
                              let uu____92154 =
                                let uu____92156 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____92156
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____92154
                            else ());
                           (let uu____92160 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____92160 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____92169 =
                                    let uu____92172 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _92175  ->
                                         FStar_Pervasives_Native.Some _92175)
                                      uu____92172
                                     in
                                  solve_prob orig uu____92169 [] wl1  in
                                let uu____92176 = attempt [base_prob] wl2  in
                                solve env uu____92176))))
           in
        let uu____92177 = FStar_Util.physical_equality c1 c2  in
        if uu____92177
        then
          let uu____92180 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____92180
        else
          ((let uu____92184 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____92184
            then
              let uu____92189 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____92191 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____92189
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____92191
            else ());
           (let uu____92196 =
              let uu____92205 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____92208 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____92205, uu____92208)  in
            match uu____92196 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92226),FStar_Syntax_Syntax.Total
                    (t2,uu____92228)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____92245 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92245 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92247,FStar_Syntax_Syntax.Total uu____92248) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92267),FStar_Syntax_Syntax.Total
                    (t2,uu____92269)) ->
                     let uu____92286 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92286 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____92289),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92291)) ->
                     let uu____92308 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92308 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____92311),FStar_Syntax_Syntax.GTotal
                    (t2,uu____92313)) ->
                     let uu____92330 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____92330 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____92332,FStar_Syntax_Syntax.Comp uu____92333) ->
                     let uu____92342 =
                       let uu___4158_92345 = problem  in
                       let uu____92348 =
                         let uu____92349 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92349
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92345.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92348;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92345.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92345.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92345.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92345.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92345.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92345.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92345.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92345.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92342 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____92350,FStar_Syntax_Syntax.Comp uu____92351) ->
                     let uu____92360 =
                       let uu___4158_92363 = problem  in
                       let uu____92366 =
                         let uu____92367 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92367
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4158_92363.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____92366;
                         FStar_TypeChecker_Common.relation =
                           (uu___4158_92363.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___4158_92363.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___4158_92363.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4158_92363.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4158_92363.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4158_92363.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4158_92363.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4158_92363.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92360 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92368,FStar_Syntax_Syntax.GTotal uu____92369) ->
                     let uu____92378 =
                       let uu___4170_92381 = problem  in
                       let uu____92384 =
                         let uu____92385 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92385
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92381.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92381.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92381.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92384;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92381.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92381.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92381.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92381.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92381.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92381.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92378 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92386,FStar_Syntax_Syntax.Total uu____92387) ->
                     let uu____92396 =
                       let uu___4170_92399 = problem  in
                       let uu____92402 =
                         let uu____92403 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____92403
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___4170_92399.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___4170_92399.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___4170_92399.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____92402;
                         FStar_TypeChecker_Common.element =
                           (uu___4170_92399.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___4170_92399.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___4170_92399.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___4170_92399.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___4170_92399.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___4170_92399.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____92396 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____92404,FStar_Syntax_Syntax.Comp uu____92405) ->
                     let uu____92406 =
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
                     if uu____92406
                     then
                       let uu____92409 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____92409 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____92416 =
                            let uu____92421 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____92421
                            then (c1_comp, c2_comp)
                            else
                              (let uu____92430 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____92431 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____92430, uu____92431))
                             in
                          match uu____92416 with
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
                           (let uu____92439 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____92439
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____92447 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____92447 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____92450 =
                                  let uu____92452 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____92454 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____92452 uu____92454
                                   in
                                giveup env uu____92450 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____92465 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____92465 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____92515 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____92515 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____92540 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____92571  ->
                match uu____92571 with
                | (u1,u2) ->
                    let uu____92579 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____92581 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____92579 uu____92581))
         in
      FStar_All.pipe_right uu____92540 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____92618,[])) when
          let uu____92645 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____92645 -> "{}"
      | uu____92648 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____92675 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____92675
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____92687 =
              FStar_List.map
                (fun uu____92700  ->
                   match uu____92700 with
                   | (uu____92707,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____92687 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____92718 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____92718 imps
  
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
                  let uu____92775 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____92775
                  then
                    let uu____92783 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____92785 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____92783
                      (rel_to_string rel) uu____92785
                  else "TOP"  in
                let uu____92791 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____92791 with
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
              let uu____92851 =
                let uu____92854 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _92857  -> FStar_Pervasives_Native.Some _92857)
                  uu____92854
                 in
              FStar_Syntax_Syntax.new_bv uu____92851 t1  in
            let uu____92858 =
              let uu____92863 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____92863
               in
            match uu____92858 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____92923 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____92923
         then
           let uu____92928 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____92928
         else ());
        (let uu____92935 =
           FStar_Util.record_time (fun uu____92942  -> solve env probs)  in
         match uu____92935 with
         | (sol,ms) ->
             ((let uu____92954 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____92954
               then
                 let uu____92959 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____92959
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____92972 =
                     FStar_Util.record_time
                       (fun uu____92979  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____92972 with
                    | ((),ms1) ->
                        ((let uu____92990 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____92990
                          then
                            let uu____92995 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____92995
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____93009 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____93009
                     then
                       let uu____93016 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____93016
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
          ((let uu____93043 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____93043
            then
              let uu____93048 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____93048
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____93055 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____93055
             then
               let uu____93060 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____93060
             else ());
            (let f2 =
               let uu____93066 =
                 let uu____93067 = FStar_Syntax_Util.unmeta f1  in
                 uu____93067.FStar_Syntax_Syntax.n  in
               match uu____93066 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____93071 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4286_93072 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___4286_93072.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___4286_93072.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___4286_93072.FStar_TypeChecker_Env.implicits)
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
            let uu____93127 =
              let uu____93128 =
                let uu____93129 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _93130  ->
                       FStar_TypeChecker_Common.NonTrivial _93130)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____93129;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____93128  in
            FStar_All.pipe_left
              (fun _93137  -> FStar_Pervasives_Native.Some _93137)
              uu____93127
  
let with_guard_no_simp :
  'Auu____93147 .
    'Auu____93147 ->
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
            let uu____93170 =
              let uu____93171 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _93172  -> FStar_TypeChecker_Common.NonTrivial _93172)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____93171;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____93170
  
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
          (let uu____93205 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____93205
           then
             let uu____93210 = FStar_Syntax_Print.term_to_string t1  in
             let uu____93212 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____93210
               uu____93212
           else ());
          (let uu____93217 =
             let uu____93222 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____93222
              in
           match uu____93217 with
           | (prob,wl) ->
               let g =
                 let uu____93230 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____93240  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____93230  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____93276 = try_teq true env t1 t2  in
        match uu____93276 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____93281 = FStar_TypeChecker_Env.get_range env  in
              let uu____93282 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____93281 uu____93282);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____93290 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____93290
              then
                let uu____93295 = FStar_Syntax_Print.term_to_string t1  in
                let uu____93297 = FStar_Syntax_Print.term_to_string t2  in
                let uu____93299 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____93295
                  uu____93297 uu____93299
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
          let uu____93325 = FStar_TypeChecker_Env.get_range env  in
          let uu____93326 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____93325 uu____93326
  
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
        (let uu____93355 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____93355
         then
           let uu____93360 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____93362 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____93360 uu____93362
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____93373 =
           let uu____93380 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____93380 "sub_comp"
            in
         match uu____93373 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____93393 =
                 FStar_Util.record_time
                   (fun uu____93405  ->
                      let uu____93406 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____93417  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____93406)
                  in
               match uu____93393 with
               | (r,ms) ->
                   ((let uu____93448 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____93448
                     then
                       let uu____93453 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____93455 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____93457 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____93453 uu____93455
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____93457
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
      fun uu____93495  ->
        match uu____93495 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____93538 =
                 let uu____93544 =
                   let uu____93546 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____93548 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____93546 uu____93548
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____93544)  in
               let uu____93552 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____93538 uu____93552)
               in
            let equiv1 v1 v' =
              let uu____93565 =
                let uu____93570 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____93571 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____93570, uu____93571)  in
              match uu____93565 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____93591 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____93622 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____93622 with
                      | FStar_Syntax_Syntax.U_unif uu____93629 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____93658  ->
                                    match uu____93658 with
                                    | (u,v') ->
                                        let uu____93667 = equiv1 v1 v'  in
                                        if uu____93667
                                        then
                                          let uu____93672 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____93672 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____93693 -> []))
               in
            let uu____93698 =
              let wl =
                let uu___4377_93702 = empty_worklist env  in
                {
                  attempting = (uu___4377_93702.attempting);
                  wl_deferred = (uu___4377_93702.wl_deferred);
                  ctr = (uu___4377_93702.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4377_93702.smt_ok);
                  umax_heuristic_ok = (uu___4377_93702.umax_heuristic_ok);
                  tcenv = (uu___4377_93702.tcenv);
                  wl_implicits = (uu___4377_93702.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____93721  ->
                      match uu____93721 with
                      | (lb,v1) ->
                          let uu____93728 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____93728 with
                           | USolved wl1 -> ()
                           | uu____93731 -> fail1 lb v1)))
               in
            let rec check_ineq uu____93742 =
              match uu____93742 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____93754) -> true
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
                      uu____93778,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____93780,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____93791) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____93799,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____93808 -> false)
               in
            let uu____93814 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____93831  ->
                      match uu____93831 with
                      | (u,v1) ->
                          let uu____93839 = check_ineq (u, v1)  in
                          if uu____93839
                          then true
                          else
                            ((let uu____93847 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____93847
                              then
                                let uu____93852 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____93854 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____93852
                                  uu____93854
                              else ());
                             false)))
               in
            if uu____93814
            then ()
            else
              ((let uu____93864 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____93864
                then
                  ((let uu____93870 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____93870);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____93882 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____93882))
                else ());
               (let uu____93895 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____93895))
  
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
        let fail1 uu____93969 =
          match uu____93969 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4454_93995 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___4454_93995.attempting);
            wl_deferred = (uu___4454_93995.wl_deferred);
            ctr = (uu___4454_93995.ctr);
            defer_ok;
            smt_ok = (uu___4454_93995.smt_ok);
            umax_heuristic_ok = (uu___4454_93995.umax_heuristic_ok);
            tcenv = (uu___4454_93995.tcenv);
            wl_implicits = (uu___4454_93995.wl_implicits)
          }  in
        (let uu____93998 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____93998
         then
           let uu____94003 = FStar_Util.string_of_bool defer_ok  in
           let uu____94005 = wl_to_string wl  in
           let uu____94007 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____94003 uu____94005 uu____94007
         else ());
        (let g1 =
           let uu____94013 = solve_and_commit env wl fail1  in
           match uu____94013 with
           | FStar_Pervasives_Native.Some
               (uu____94020::uu____94021,uu____94022) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4469_94051 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4469_94051.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4469_94051.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____94052 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4474_94061 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4474_94061.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4474_94061.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4474_94061.FStar_TypeChecker_Env.implicits)
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
    let uu____94115 = FStar_ST.op_Bang last_proof_ns  in
    match uu____94115 with
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
            let uu___4493_94240 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4493_94240.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4493_94240.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4493_94240.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____94241 =
            let uu____94243 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____94243  in
          if uu____94241
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____94255 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____94256 =
                       let uu____94258 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____94258
                        in
                     FStar_Errors.diag uu____94255 uu____94256)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____94266 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____94267 =
                        let uu____94269 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____94269
                         in
                      FStar_Errors.diag uu____94266 uu____94267)
                   else ();
                   (let uu____94275 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____94275
                      "discharge_guard'" env vc1);
                   (let uu____94277 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____94277 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____94286 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94287 =
                                let uu____94289 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____94289
                                 in
                              FStar_Errors.diag uu____94286 uu____94287)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____94299 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____94300 =
                                let uu____94302 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____94302
                                 in
                              FStar_Errors.diag uu____94299 uu____94300)
                           else ();
                           (let vcs =
                              let uu____94316 = FStar_Options.use_tactics ()
                                 in
                              if uu____94316
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____94338  ->
                                     (let uu____94340 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____94340);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____94384  ->
                                              match uu____94384 with
                                              | (env1,goal,opts) ->
                                                  let uu____94400 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____94400, opts)))))
                              else
                                (let uu____94403 =
                                   let uu____94410 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____94410)  in
                                 [uu____94403])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____94443  ->
                                    match uu____94443 with
                                    | (env1,goal,opts) ->
                                        let uu____94453 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____94453 with
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
                                                (let uu____94465 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94466 =
                                                   let uu____94468 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____94470 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____94468 uu____94470
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94465 uu____94466)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____94477 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____94478 =
                                                   let uu____94480 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____94480
                                                    in
                                                 FStar_Errors.diag
                                                   uu____94477 uu____94478)
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
      let uu____94498 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____94498 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____94507 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____94507
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____94521 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____94521 with
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
        let uu____94551 = try_teq false env t1 t2  in
        match uu____94551 with
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
            let uu____94595 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____94595 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____94608 ->
                     let uu____94621 =
                       let uu____94622 = FStar_Syntax_Subst.compress r  in
                       uu____94622.FStar_Syntax_Syntax.n  in
                     (match uu____94621 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____94627) ->
                          unresolved ctx_u'
                      | uu____94644 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____94668 = acc  in
            match uu____94668 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____94687 = hd1  in
                     (match uu____94687 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____94698 = unresolved ctx_u  in
                             if uu____94698
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____94722 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____94722
                                     then
                                       let uu____94726 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____94726
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____94735 = teq_nosmt env1 t tm
                                          in
                                       match uu____94735 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4606_94745 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4606_94745.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4606_94745.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4606_94745.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4606_94745.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4606_94745.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4606_94745.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4606_94745.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4609_94753 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4609_94753.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4609_94753.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4609_94753.FStar_TypeChecker_Env.imp_range)
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
                                    let uu___4613_94764 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4613_94764.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4613_94764.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4613_94764.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4613_94764.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4613_94764.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4613_94764.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4613_94764.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4613_94764.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4613_94764.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___4613_94764.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4613_94764.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4613_94764.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4613_94764.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4613_94764.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4613_94764.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4613_94764.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4613_94764.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4613_94764.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4613_94764.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4613_94764.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4613_94764.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4613_94764.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4613_94764.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4613_94764.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4613_94764.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4613_94764.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4613_94764.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4613_94764.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4613_94764.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4613_94764.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4613_94764.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4613_94764.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4613_94764.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4613_94764.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4613_94764.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4613_94764.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4613_94764.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4613_94764.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4613_94764.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4613_94764.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4613_94764.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4613_94764.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4618_94768 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4618_94768.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4618_94768.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4618_94768.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4618_94768.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4618_94768.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4618_94768.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4618_94768.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4618_94768.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4618_94768.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4618_94768.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___4618_94768.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4618_94768.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4618_94768.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4618_94768.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4618_94768.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4618_94768.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4618_94768.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4618_94768.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4618_94768.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4618_94768.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4618_94768.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4618_94768.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4618_94768.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4618_94768.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4618_94768.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4618_94768.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4618_94768.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4618_94768.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4618_94768.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4618_94768.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4618_94768.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4618_94768.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4618_94768.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4618_94768.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4618_94768.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4618_94768.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4618_94768.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4618_94768.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4618_94768.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4618_94768.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4618_94768.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4618_94768.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____94773 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____94773
                                   then
                                     let uu____94778 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____94780 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____94782 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____94784 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____94778 uu____94780 uu____94782
                                       reason uu____94784
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4624_94791  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____94798 =
                                             let uu____94808 =
                                               let uu____94816 =
                                                 let uu____94818 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____94820 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____94822 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____94818 uu____94820
                                                   uu____94822
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____94816, r)
                                                in
                                             [uu____94808]  in
                                           FStar_Errors.add_errors
                                             uu____94798);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___4632_94842 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___4632_94842.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___4632_94842.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___4632_94842.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____94846 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____94857  ->
                                               let uu____94858 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____94860 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____94862 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____94858 uu____94860
                                                 reason uu____94862)) env2 g2
                                         true
                                        in
                                     match uu____94846 with
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
          let uu___4640_94870 = g  in
          let uu____94871 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4640_94870.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4640_94870.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4640_94870.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____94871
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
        let uu____94914 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____94914 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____94915 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____94915
      | imp::uu____94917 ->
          let uu____94920 =
            let uu____94926 =
              let uu____94928 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____94930 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____94928 uu____94930 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____94926)
             in
          FStar_Errors.raise_error uu____94920
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____94952 = teq_nosmt env t1 t2  in
        match uu____94952 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4662_94971 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4662_94971.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4662_94971.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4662_94971.FStar_TypeChecker_Env.implicits)
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
        (let uu____95007 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95007
         then
           let uu____95012 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95014 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____95012
             uu____95014
         else ());
        (let uu____95019 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95019 with
         | (prob,x,wl) ->
             let g =
               let uu____95038 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____95049  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95038  in
             ((let uu____95070 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____95070
               then
                 let uu____95075 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____95077 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____95079 =
                   let uu____95081 = FStar_Util.must g  in
                   guard_to_string env uu____95081  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____95075 uu____95077 uu____95079
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
        let uu____95118 = check_subtyping env t1 t2  in
        match uu____95118 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95137 =
              let uu____95138 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____95138 g  in
            FStar_Pervasives_Native.Some uu____95137
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95157 = check_subtyping env t1 t2  in
        match uu____95157 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____95176 =
              let uu____95177 =
                let uu____95178 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____95178]  in
              FStar_TypeChecker_Env.close_guard env uu____95177 g  in
            FStar_Pervasives_Native.Some uu____95176
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____95216 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____95216
         then
           let uu____95221 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____95223 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____95221
             uu____95223
         else ());
        (let uu____95228 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____95228 with
         | (prob,x,wl) ->
             let g =
               let uu____95243 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____95254  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____95243  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____95278 =
                      let uu____95279 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____95279]  in
                    FStar_TypeChecker_Env.close_guard env uu____95278 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____95320 = subtype_nosmt env t1 t2  in
        match uu____95320 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  