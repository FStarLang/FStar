open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f  ->
    let uf = FStar_Syntax_Unionfind.get ()  in
    FStar_Thunk.mk
      (fun uu____40  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         FStar_Syntax_Unionfind.set uf;
         (let r = f ()  in FStar_Syntax_Unionfind.rollback tx; r))
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____78 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____113 -> false
  
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
                    let uu____570 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____570;
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
                   (let uu____604 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____604
                    then
                      let uu____608 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____608
                    else ());
                   (ctx_uvar, t,
                     ((let uu___77_614 = wl  in
                       {
                         attempting = (uu___77_614.attempting);
                         wl_deferred = (uu___77_614.wl_deferred);
                         ctr = (uu___77_614.ctr);
                         defer_ok = (uu___77_614.defer_ok);
                         smt_ok = (uu___77_614.smt_ok);
                         umax_heuristic_ok = (uu___77_614.umax_heuristic_ok);
                         tcenv = (uu___77_614.tcenv);
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
            let uu___83_647 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___83_647.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___83_647.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___83_647.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___83_647.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___83_647.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___83_647.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___83_647.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___83_647.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___83_647.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___83_647.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___83_647.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___83_647.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___83_647.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___83_647.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___83_647.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___83_647.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___83_647.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___83_647.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___83_647.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___83_647.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___83_647.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___83_647.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___83_647.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___83_647.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___83_647.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___83_647.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___83_647.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___83_647.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___83_647.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___83_647.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___83_647.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___83_647.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___83_647.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___83_647.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___83_647.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___83_647.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___83_647.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___83_647.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___83_647.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___83_647.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___83_647.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___83_647.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___83_647.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___83_647.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___83_647.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____649 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____649 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____736 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____771 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____801 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____812 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____823 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_841  ->
    match uu___0_841 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____853 = FStar_Syntax_Util.head_and_args t  in
    match uu____853 with
    | (head,args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____916 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____918 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____933 =
                     let uu____935 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____935  in
                   FStar_Util.format1 "@<%s>" uu____933
                in
             let uu____939 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____916 uu____918 uu____939
         | uu____942 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_954  ->
      match uu___1_954 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____959 =
            let uu____963 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____965 =
              let uu____969 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____971 =
                let uu____975 =
                  let uu____979 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____979]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____975
                 in
              uu____969 :: uu____971  in
            uu____963 :: uu____965  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____959
      | FStar_TypeChecker_Common.CProb p ->
          let uu____990 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____992 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____994 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____990 uu____992
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____994
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1008  ->
      match uu___2_1008 with
      | UNIV (u,t) ->
          let x =
            let uu____1014 = FStar_Options.hide_uvar_nums ()  in
            if uu____1014
            then "?"
            else
              (let uu____1021 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1021 FStar_Util.string_of_int)
             in
          let uu____1025 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1025
      | TERM (u,t) ->
          let x =
            let uu____1032 = FStar_Options.hide_uvar_nums ()  in
            if uu____1032
            then "?"
            else
              (let uu____1039 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1039 FStar_Util.string_of_int)
             in
          let uu____1043 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s <- %s" x uu____1043
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  -> FStar_Common.string_of_list (uvi_to_string env) uvis
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1073 =
      let uu____1077 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1077
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1073 (FStar_String.concat ", ")
  
let args_to_string :
  'uuuuuu1096 .
    (FStar_Syntax_Syntax.term * 'uuuuuu1096) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1115 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1136  ->
              match uu____1136 with
              | (x,uu____1143) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1115 (FStar_String.concat " ")
  
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
        (let uu____1183 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1183
         then
           let uu____1188 = FStar_Thunk.force reason  in
           let uu____1191 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1188 uu____1191
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1214 = mklstr (fun uu____1217  -> reason)  in
        giveup env uu____1214 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1223  ->
    match uu___3_1223 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'uuuuuu1229 .
    'uuuuuu1229 FStar_TypeChecker_Common.problem ->
      'uuuuuu1229 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___147_1241 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___147_1241.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___147_1241.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___147_1241.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___147_1241.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___147_1241.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___147_1241.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___147_1241.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'uuuuuu1249 .
    'uuuuuu1249 FStar_TypeChecker_Common.problem ->
      'uuuuuu1249 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1269  ->
    match uu___4_1269 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1275  -> FStar_TypeChecker_Common.TProb uu____1275)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1281  -> FStar_TypeChecker_Common.CProb uu____1281)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1287  ->
    match uu___5_1287 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___159_1293 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___159_1293.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___159_1293.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___159_1293.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___159_1293.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___159_1293.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___159_1293.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___159_1293.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___159_1293.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___159_1293.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___163_1301 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___163_1301.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___163_1301.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___163_1301.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___163_1301.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___163_1301.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___163_1301.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___163_1301.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___163_1301.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___163_1301.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1314  ->
      match uu___6_1314 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1321  ->
    match uu___7_1321 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1334  ->
    match uu___8_1334 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1349  ->
    match uu___9_1349 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1364  ->
    match uu___10_1364 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1378  ->
    match uu___11_1378 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1392  ->
    match uu___12_1392 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1404  ->
    match uu___13_1404 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'uuuuuu1420 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu1420) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1450 =
          let uu____1452 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1452  in
        if uu____1450
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1489)::bs ->
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
          let uu____1536 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1560 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1560]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1536
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1588 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1612 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1612]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1588
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1659 =
          let uu____1661 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1661  in
        if uu____1659
        then ()
        else
          (let uu____1666 =
             let uu____1669 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1669
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1666 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1718 =
          let uu____1720 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1720  in
        if uu____1718
        then ()
        else
          (let uu____1725 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1725)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1745 =
        let uu____1747 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1747  in
      if uu____1745
      then ()
      else
        (let msgf m =
           let uu____1761 =
             let uu____1763 =
               let uu____1765 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1765 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1763  in
           Prims.op_Hat msg uu____1761  in
         (let uu____1770 = msgf "scope"  in
          let uu____1773 = p_scope prob  in
          def_scope_wf uu____1770 (p_loc prob) uu____1773);
         (let uu____1785 = msgf "guard"  in
          def_check_scoped uu____1785 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1792 = msgf "lhs"  in
                def_check_scoped uu____1792 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1795 = msgf "rhs"  in
                def_check_scoped uu____1795 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1802 = msgf "lhs"  in
                def_check_scoped_comp uu____1802 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1805 = msgf "rhs"  in
                def_check_scoped_comp uu____1805 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___256_1826 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___256_1826.wl_deferred);
          ctr = (uu___256_1826.ctr);
          defer_ok = (uu___256_1826.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___256_1826.umax_heuristic_ok);
          tcenv = (uu___256_1826.tcenv);
          wl_implicits = (uu___256_1826.wl_implicits)
        }
  
let wl_of_guard :
  'uuuuuu1834 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1834 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___260_1857 = empty_worklist env  in
      let uu____1858 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1858;
        wl_deferred = (uu___260_1857.wl_deferred);
        ctr = (uu___260_1857.ctr);
        defer_ok = (uu___260_1857.defer_ok);
        smt_ok = (uu___260_1857.smt_ok);
        umax_heuristic_ok = (uu___260_1857.umax_heuristic_ok);
        tcenv = (uu___260_1857.tcenv);
        wl_implicits = (uu___260_1857.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___265_1879 = wl  in
        {
          attempting = (uu___265_1879.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___265_1879.ctr);
          defer_ok = (uu___265_1879.defer_ok);
          smt_ok = (uu___265_1879.smt_ok);
          umax_heuristic_ok = (uu___265_1879.umax_heuristic_ok);
          tcenv = (uu___265_1879.tcenv);
          wl_implicits = (uu___265_1879.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1906 = FStar_Thunk.mkv reason  in defer uu____1906 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___273_1925 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___273_1925.wl_deferred);
         ctr = (uu___273_1925.ctr);
         defer_ok = (uu___273_1925.defer_ok);
         smt_ok = (uu___273_1925.smt_ok);
         umax_heuristic_ok = (uu___273_1925.umax_heuristic_ok);
         tcenv = (uu___273_1925.tcenv);
         wl_implicits = (uu___273_1925.wl_implicits)
       })
  
let mk_eq2 :
  'uuuuuu1939 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu1939 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1973 = FStar_Syntax_Util.type_u ()  in
            match uu____1973 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1985 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1985 with
                 | (uu____2003,tt,wl1) ->
                     let uu____2006 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2006, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2012  ->
    match uu___14_2012 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2018  -> FStar_TypeChecker_Common.TProb uu____2018)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2024  -> FStar_TypeChecker_Common.CProb uu____2024)
          (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2032 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2032 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2052  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'uuuuuu2094 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2094 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2094 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2094 FStar_TypeChecker_Common.problem * worklist)
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
                        let uu____2181 =
                          let uu____2190 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2190]  in
                        FStar_List.append scope uu____2181
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2233 =
                      let uu____2236 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2236  in
                    FStar_List.append uu____2233
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2255 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2255 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2281 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2281;
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
                  (let uu____2355 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2355 with
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
                  (let uu____2443 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2443 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'uuuuuu2481 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2481 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2481 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2481 FStar_TypeChecker_Common.problem * worklist)
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
                          let uu____2549 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2549]  in
                        let uu____2568 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2568
                     in
                  let uu____2571 =
                    let uu____2578 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___356_2589 = wl  in
                       {
                         attempting = (uu___356_2589.attempting);
                         wl_deferred = (uu___356_2589.wl_deferred);
                         ctr = (uu___356_2589.ctr);
                         defer_ok = (uu___356_2589.defer_ok);
                         smt_ok = (uu___356_2589.smt_ok);
                         umax_heuristic_ok =
                           (uu___356_2589.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___356_2589.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2578
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2571 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2607 =
                              let uu____2612 =
                                let uu____2613 =
                                  let uu____2622 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2622
                                   in
                                [uu____2613]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2612  in
                            uu____2607 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2650 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2650;
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
                let uu____2698 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2698;
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
  'uuuuuu2713 .
    worklist ->
      'uuuuuu2713 FStar_TypeChecker_Common.problem ->
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
              let uu____2746 =
                let uu____2749 =
                  let uu____2750 =
                    let uu____2757 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2757)  in
                  FStar_Syntax_Syntax.NT uu____2750  in
                [uu____2749]  in
              FStar_Syntax_Subst.subst uu____2746 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2779 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2779
        then
          let uu____2787 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2790 = prob_to_string env d  in
          let uu____2792 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2799 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2787 uu____2790 uu____2792 uu____2799
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2811 -> failwith "impossible"  in
           let uu____2814 =
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
           match uu____2814 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2857  ->
            match uu___15_2857 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2871 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2875 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2875 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2906  ->
           match uu___16_2906 with
           | UNIV uu____2909 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2916 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2916
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
        (fun uu___17_2944  ->
           match uu___17_2944 with
           | UNIV (u',t) ->
               let uu____2949 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2949
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2956 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2968 =
        let uu____2969 =
          let uu____2970 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2970
           in
        FStar_Syntax_Subst.compress uu____2969  in
      FStar_All.pipe_right uu____2968 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2982 =
        let uu____2983 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2983  in
      FStar_All.pipe_right uu____2982 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2995 =
        let uu____2999 =
          let uu____3001 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3001  in
        FStar_Pervasives_Native.Some uu____2999  in
      FStar_Profiling.profile (fun uu____3004  -> sn' env t) uu____2995
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
          let uu____3029 =
            let uu____3033 =
              let uu____3035 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3035  in
            FStar_Pervasives_Native.Some uu____3033  in
          FStar_Profiling.profile
            (fun uu____3038  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3029
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3046 = FStar_Syntax_Util.head_and_args t  in
    match uu____3046 with
    | (h,uu____3065) ->
        let uu____3090 =
          let uu____3091 = FStar_Syntax_Subst.compress h  in
          uu____3091.FStar_Syntax_Syntax.n  in
        (match uu____3090 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3096 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3109 =
        let uu____3113 =
          let uu____3115 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3115  in
        FStar_Pervasives_Native.Some uu____3113  in
      FStar_Profiling.profile
        (fun uu____3120  ->
           let uu____3121 = should_strongly_reduce t  in
           if uu____3121
           then
             let uu____3124 =
               let uu____3125 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3125  in
             FStar_All.pipe_right uu____3124 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3109 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'uuuuuu3136 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3136) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3136)
  =
  fun env  ->
    fun t  ->
      let uu____3159 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3159, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3211  ->
              match uu____3211 with
              | (x,imp) ->
                  let uu____3230 =
                    let uu___462_3231 = x  in
                    let uu____3232 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___462_3231.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___462_3231.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3232
                    }  in
                  (uu____3230, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3256 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3256
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3260 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3260
        | uu____3263 -> u2  in
      let uu____3264 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3264
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3281 =
          let uu____3285 =
            let uu____3287 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3287  in
          FStar_Pervasives_Native.Some uu____3285  in
        FStar_Profiling.profile
          (fun uu____3290  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3281 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
        let rec aux norm t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3412 = norm_refinement env t12  in
                 match uu____3412 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3427;
                     FStar_Syntax_Syntax.vars = uu____3428;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3452 =
                       let uu____3454 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3456 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3454 uu____3456
                        in
                     failwith uu____3452)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3472 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm uu____3472
          | FStar_Syntax_Syntax.Tm_uinst uu____3473 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3510 =
                   let uu____3511 = FStar_Syntax_Subst.compress t1'  in
                   uu____3511.FStar_Syntax_Syntax.n  in
                 match uu____3510 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3526 -> aux true t1'
                 | uu____3534 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3549 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3580 =
                   let uu____3581 = FStar_Syntax_Subst.compress t1'  in
                   uu____3581.FStar_Syntax_Syntax.n  in
                 match uu____3580 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3596 -> aux true t1'
                 | uu____3604 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3619 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3666 =
                   let uu____3667 = FStar_Syntax_Subst.compress t1'  in
                   uu____3667.FStar_Syntax_Syntax.n  in
                 match uu____3666 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3682 -> aux true t1'
                 | uu____3690 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3705 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3720 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3735 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3750 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3765 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3794 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3827 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3848 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3875 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3903 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3940 ->
              let uu____3947 =
                let uu____3949 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3951 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3949 uu____3951
                 in
              failwith uu____3947
          | FStar_Syntax_Syntax.Tm_ascribed uu____3966 ->
              let uu____3993 =
                let uu____3995 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3997 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3995 uu____3997
                 in
              failwith uu____3993
          | FStar_Syntax_Syntax.Tm_delayed uu____4012 ->
              let uu____4027 =
                let uu____4029 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4031 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4029 uu____4031
                 in
              failwith uu____4027
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4046 =
                let uu____4048 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4050 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4048 uu____4050
                 in
              failwith uu____4046
           in
        let uu____4065 = whnf env t1  in aux false uu____4065
  
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
      let uu____4110 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4110 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4151 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4151, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta  ->
    fun env  ->
      fun t  ->
        let uu____4178 = base_and_refinement_maybe_delta delta env t  in
        match uu____4178 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4238  ->
    match uu____4238 with
    | (t_base,refopt) ->
        let uu____4269 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4269 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4311 =
      let uu____4315 =
        let uu____4318 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4343  ->
                  match uu____4343 with | (uu____4351,uu____4352,x) -> x))
           in
        FStar_List.append wl.attempting uu____4318  in
      FStar_List.map (wl_prob_to_string wl) uu____4315  in
    FStar_All.pipe_right uu____4311 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'uuuuuu4373 .
    ('uuuuuu4373 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4385  ->
    match uu____4385 with
    | (uu____4392,c,args) ->
        let uu____4395 = print_ctx_uvar c  in
        let uu____4397 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4395 uu____4397
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4407 = FStar_Syntax_Util.head_and_args t  in
    match uu____4407 with
    | (head,_args) ->
        let uu____4451 =
          let uu____4452 = FStar_Syntax_Subst.compress head  in
          uu____4452.FStar_Syntax_Syntax.n  in
        (match uu____4451 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4456 -> true
         | uu____4470 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4478 = FStar_Syntax_Util.head_and_args t  in
    match uu____4478 with
    | (head,_args) ->
        let uu____4521 =
          let uu____4522 = FStar_Syntax_Subst.compress head  in
          uu____4522.FStar_Syntax_Syntax.n  in
        (match uu____4521 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4526) -> u
         | uu____4543 -> failwith "Not a flex-uvar")
  
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0  ->
    fun wl  ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x  in
        let t_x' = FStar_Syntax_Subst.subst' s t_x  in
        let uu____4579 =
          let uu____4580 = FStar_Syntax_Subst.compress t_x'  in
          uu____4580.FStar_Syntax_Syntax.n  in
        match uu____4579 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____4585 -> false  in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____4601 -> true  in
      let uu____4603 = FStar_Syntax_Util.head_and_args t0  in
      match uu____4603 with
      | (head,args) ->
          let uu____4650 =
            let uu____4651 = FStar_Syntax_Subst.compress head  in
            uu____4651.FStar_Syntax_Syntax.n  in
          (match uu____4650 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4659)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,uu____4675) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4716 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               (match uu____4716 with
                | (gamma_aff,new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____4743 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff
                            in
                         let uu____4747 =
                           let uu____4754 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma
                              in
                           let uu____4763 =
                             let uu____4766 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             FStar_Syntax_Util.arrow dom_binders uu____4766
                              in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____4754
                             uu____4763
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta
                            in
                         (match uu____4747 with
                          | (v,t_v,wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____4802  ->
                                     match uu____4802 with
                                     | (x,i) ->
                                         let uu____4821 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____4821, i)) dom_binders
                                 in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  FStar_Pervasives_Native.None
                                  t0.FStar_Syntax_Syntax.pos
                                 in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____4853  ->
                                       match uu____4853 with
                                       | (a,i) ->
                                           let uu____4872 =
                                             FStar_Syntax_Subst.subst' s a
                                              in
                                           (uu____4872, i)) args_sol
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    FStar_Pervasives_Native.None
                                    t0.FStar_Syntax_Syntax.pos
                                   in
                                (t, wl1))))))
           | uu____4884 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
  
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t  ->
    let uu____4896 = FStar_Syntax_Util.head_and_args t  in
    match uu____4896 with
    | (head,args) ->
        let uu____4939 =
          let uu____4940 = FStar_Syntax_Subst.compress head  in
          uu____4940.FStar_Syntax_Syntax.n  in
        (match uu____4939 with
         | FStar_Syntax_Syntax.Tm_uvar (uv,s) -> (t, uv, args)
         | uu____4961 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t  ->
    fun wl  ->
      let uu____4982 = ensure_no_uvar_subst t wl  in
      match uu____4982 with
      | (t1,wl1) ->
          let uu____4993 = destruct_flex_t' t1  in (uu____4993, wl1)
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5010 =
          let uu____5033 =
            let uu____5034 = FStar_Syntax_Subst.compress k  in
            uu____5034.FStar_Syntax_Syntax.n  in
          match uu____5033 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5116 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5116)
              else
                (let uu____5151 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5151 with
                 | (ys',t1,uu____5184) ->
                     let uu____5189 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5189))
          | uu____5228 ->
              let uu____5229 =
                let uu____5234 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5234)  in
              ((ys, t), uu____5229)
           in
        match uu____5010 with
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
                 let uu____5329 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5329 c  in
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
               (let uu____5407 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5407
                then
                  let uu____5412 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5414 = print_ctx_uvar uv  in
                  let uu____5416 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5412 uu____5414 uu____5416
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5425 =
                   let uu____5427 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5427  in
                 let uu____5430 =
                   let uu____5433 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5433
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5425 uu____5430 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail uu____5466 =
               let uu____5467 =
                 let uu____5469 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5471 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5469 uu____5471
                  in
               failwith uu____5467  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5537  ->
                       match uu____5537 with
                       | (a,i) ->
                           let uu____5558 =
                             let uu____5559 = FStar_Syntax_Subst.compress a
                                in
                             uu____5559.FStar_Syntax_Syntax.n  in
                           (match uu____5558 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5585 -> (fail (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5595 =
                 let uu____5597 = is_flex g  in Prims.op_Negation uu____5597
                  in
               if uu____5595
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____5606 = destruct_flex_t g wl  in
                  match uu____5606 with
                  | ((uu____5611,uv1,args),wl1) ->
                      ((let uu____5616 = args_as_binders args  in
                        assign_solution uu____5616 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___731_5618 = wl1  in
              {
                attempting = (uu___731_5618.attempting);
                wl_deferred = (uu___731_5618.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___731_5618.defer_ok);
                smt_ok = (uu___731_5618.smt_ok);
                umax_heuristic_ok = (uu___731_5618.umax_heuristic_ok);
                tcenv = (uu___731_5618.tcenv);
                wl_implicits = (uu___731_5618.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5643 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5643
         then
           let uu____5648 = FStar_Util.string_of_int pid  in
           let uu____5650 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5648 uu____5650
         else ());
        commit sol;
        (let uu___739_5656 = wl  in
         {
           attempting = (uu___739_5656.attempting);
           wl_deferred = (uu___739_5656.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___739_5656.defer_ok);
           smt_ok = (uu___739_5656.smt_ok);
           umax_heuristic_ok = (uu___739_5656.umax_heuristic_ok);
           tcenv = (uu___739_5656.tcenv);
           wl_implicits = (uu___739_5656.wl_implicits)
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
          (let uu____5692 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5692
           then
             let uu____5697 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5701 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5697 uu____5701
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars =
        let uu____5728 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5728 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk  ->
    fun t  ->
      let uu____5768 = occurs uk t  in
      match uu____5768 with
      | (uvars,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5807 =
                 let uu____5809 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5811 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5809 uu____5811
                  in
               FStar_Pervasives_Native.Some uu____5807)
             in
          (uvars, (Prims.op_Negation occurs1), msg)
  
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
          let uu____5922 = FStar_Syntax_Syntax.bv_eq b b'  in
          if uu____5922
          then
            let uu____5933 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5933 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5984 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6041  ->
             match uu____6041 with
             | (x,uu____6053) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6071 = FStar_List.last bs  in
      match uu____6071 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6095) ->
          let uu____6106 =
            FStar_Util.prefix_until
              (fun uu___18_6121  ->
                 match uu___18_6121 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6124 -> false) g
             in
          (match uu____6106 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6138,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6175 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6175 with
        | (pfx,uu____6185) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6197 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6197 with
             | (uu____6205,src',wl1) ->
                 (FStar_Syntax_Util.set_uvar
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
        let as_set v =
          FStar_All.pipe_right v
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____6319 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6320 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6384  ->
                  fun uu____6385  ->
                    match (uu____6384, uu____6385) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6488 =
                          let uu____6490 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6490
                           in
                        if uu____6488
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6524 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6524
                           then
                             let uu____6541 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6541)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6320 with | (isect,uu____6591) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu6627 'uuuuuu6628 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6627) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6628) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6686  ->
              fun uu____6687  ->
                match (uu____6686, uu____6687) with
                | ((a,uu____6706),(b,uu____6708)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu6724 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6724) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6755  ->
           match uu____6755 with
           | (y,uu____6762) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu6772 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6772) Prims.list ->
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
              let hd = sn env arg  in
              (match hd.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____6934 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6934
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6967 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7019 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7063 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7084 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7092  ->
    match uu___19_7092 with
    | MisMatch (d1,d2) ->
        let uu____7104 =
          let uu____7106 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7108 =
            let uu____7110 =
              let uu____7112 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7112 ")"  in
            Prims.op_Hat ") (" uu____7110  in
          Prims.op_Hat uu____7106 uu____7108  in
        Prims.op_Hat "MisMatch (" uu____7104
    | HeadMatch u ->
        let uu____7119 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7119
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7128  ->
    match uu___20_7128 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7145 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7160 =
            (let uu____7166 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7168 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7166 = uu____7168) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7160 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7177 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7177 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7188 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7212 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7222 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7241 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7241
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7242 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7243 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7244 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7257 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7271 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7295) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7301,uu____7302) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7344) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7369;
             FStar_Syntax_Syntax.index = uu____7370;
             FStar_Syntax_Syntax.sort = t2;_},uu____7372)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7380 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7381 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7382 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7397 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7404 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7424 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7424
  
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
           { FStar_Syntax_Syntax.blob = uu____7443;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7444;
             FStar_Syntax_Syntax.ltyp = uu____7445;
             FStar_Syntax_Syntax.rng = uu____7446;_},uu____7447)
            ->
            let uu____7458 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7458 t21
        | (uu____7459,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7460;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7461;
             FStar_Syntax_Syntax.ltyp = uu____7462;
             FStar_Syntax_Syntax.rng = uu____7463;_})
            ->
            let uu____7474 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7474
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7477 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____7477
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7488 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7488
            then FullMatch
            else
              (let uu____7493 =
                 let uu____7502 =
                   let uu____7505 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7505  in
                 let uu____7506 =
                   let uu____7509 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7509  in
                 (uu____7502, uu____7506)  in
               MisMatch uu____7493)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7515),FStar_Syntax_Syntax.Tm_uinst (g,uu____7517)) ->
            let uu____7526 = head_matches env f g  in
            FStar_All.pipe_right uu____7526 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7527) -> HeadMatch true
        | (uu____7529,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7533 = FStar_Const.eq_const c d  in
            if uu____7533
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7543),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7545)) ->
            let uu____7578 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7578
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7588),FStar_Syntax_Syntax.Tm_refine (y,uu____7590)) ->
            let uu____7599 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7599 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7601),uu____7602) ->
            let uu____7607 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7607 head_match
        | (uu____7608,FStar_Syntax_Syntax.Tm_refine (x,uu____7610)) ->
            let uu____7615 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7615 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7616,FStar_Syntax_Syntax.Tm_type
           uu____7617) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7619,FStar_Syntax_Syntax.Tm_arrow uu____7620) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____7651),FStar_Syntax_Syntax.Tm_app (head',uu____7653))
            ->
            let uu____7702 = head_matches env head head'  in
            FStar_All.pipe_right uu____7702 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____7704),uu____7705) ->
            let uu____7730 = head_matches env head t21  in
            FStar_All.pipe_right uu____7730 head_match
        | (uu____7731,FStar_Syntax_Syntax.Tm_app (head,uu____7733)) ->
            let uu____7758 = head_matches env t11 head  in
            FStar_All.pipe_right uu____7758 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7759,FStar_Syntax_Syntax.Tm_let
           uu____7760) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7788,FStar_Syntax_Syntax.Tm_match uu____7789) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7835,FStar_Syntax_Syntax.Tm_abs
           uu____7836) -> HeadMatch true
        | uu____7874 ->
            let uu____7879 =
              let uu____7888 = delta_depth_of_term env t11  in
              let uu____7891 = delta_depth_of_term env t21  in
              (uu____7888, uu____7891)  in
            MisMatch uu____7879
  
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
            let head =
              let uu____7960 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7960  in
            (let uu____7962 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7962
             then
               let uu____7967 = FStar_Syntax_Print.term_to_string t  in
               let uu____7969 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7967 uu____7969
             else ());
            (let uu____7974 =
               let uu____7975 = FStar_Syntax_Util.un_uinst head  in
               uu____7975.FStar_Syntax_Syntax.n  in
             match uu____7974 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7981 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7981 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7995 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7995
                        then
                          let uu____8000 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8000
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8005 ->
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
                      let uu____8023 =
                        let uu____8025 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8025 = FStar_Syntax_Util.Equal  in
                      if uu____8023
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8032 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8032
                          then
                            let uu____8037 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8039 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8037
                              uu____8039
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8044 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8196 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8196
             then
               let uu____8201 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8203 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8205 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8201
                 uu____8203 uu____8205
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8233 =
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
               match uu____8233 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8281 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8281 with
               | FStar_Pervasives_Native.None  -> fail n_delta r1 t11 t21
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
                   aux retry (n_delta + Prims.int_one) t12 t22
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
                  uu____8319),uu____8320)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8341 =
                      let uu____8350 = maybe_inline t11  in
                      let uu____8353 = maybe_inline t21  in
                      (uu____8350, uu____8353)  in
                    match uu____8341 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail n_delta r t11 t21
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
                 (uu____8396,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8397))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8418 =
                      let uu____8427 = maybe_inline t11  in
                      let uu____8430 = maybe_inline t21  in
                      (uu____8427, uu____8430)  in
                    match uu____8418 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail n_delta r t11 t21
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
             | MisMatch uu____8485 -> fail n_delta r t11 t21
             | uu____8494 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8509 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8509
           then
             let uu____8514 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8516 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8518 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8526 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8543 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8543
                    (fun uu____8578  ->
                       match uu____8578 with
                       | (t11,t21) ->
                           let uu____8586 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8588 =
                             let uu____8590 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8590  in
                           Prims.op_Hat uu____8586 uu____8588))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8514 uu____8516 uu____8518 uu____8526
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8607 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8607 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8622  ->
    match uu___21_8622 with
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
      let uu___1228_8671 = p  in
      let uu____8674 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8675 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1228_8671.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8674;
        FStar_TypeChecker_Common.relation =
          (uu___1228_8671.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8675;
        FStar_TypeChecker_Common.element =
          (uu___1228_8671.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1228_8671.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1228_8671.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1228_8671.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1228_8671.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1228_8671.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8690 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8690
            (fun uu____8695  -> FStar_TypeChecker_Common.TProb uu____8695)
      | FStar_TypeChecker_Common.CProb uu____8696 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8719 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8719 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8727 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8727 with
           | (lh,lhs_args) ->
               let uu____8774 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8774 with
                | (rh,rhs_args) ->
                    let uu____8821 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8834,FStar_Syntax_Syntax.Tm_uvar uu____8835)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8924 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8951,uu____8952)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8967,FStar_Syntax_Syntax.Tm_uvar uu____8968)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8983,FStar_Syntax_Syntax.Tm_arrow uu____8984)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_9014 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_9014.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_9014.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_9014.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_9014.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_9014.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_9014.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_9014.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_9014.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_9014.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9017,FStar_Syntax_Syntax.Tm_type uu____9018)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_9034 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_9034.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_9034.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_9034.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_9034.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_9034.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_9034.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_9034.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_9034.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_9034.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9037,FStar_Syntax_Syntax.Tm_uvar uu____9038)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_9054 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_9054.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_9054.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_9054.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_9054.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_9054.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_9054.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_9054.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_9054.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_9054.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9057,FStar_Syntax_Syntax.Tm_uvar uu____9058)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9073,uu____9074)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9089,FStar_Syntax_Syntax.Tm_uvar uu____9090)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9105,uu____9106) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8821 with
                     | (rank,tp1) ->
                         let uu____9119 =
                           FStar_All.pipe_right
                             (let uu___1299_9123 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1299_9123.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1299_9123.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1299_9123.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1299_9123.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1299_9123.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1299_9123.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1299_9123.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1299_9123.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1299_9123.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9126  ->
                                FStar_TypeChecker_Common.TProb uu____9126)
                            in
                         (rank, uu____9119))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9130 =
            FStar_All.pipe_right
              (let uu___1303_9134 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1303_9134.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1303_9134.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1303_9134.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1303_9134.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1303_9134.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1303_9134.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1303_9134.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1303_9134.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1303_9134.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9137  -> FStar_TypeChecker_Common.CProb uu____9137)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9130)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9197 probs =
      match uu____9197 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9278 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9299 = rank wl.tcenv hd  in
               (match uu____9299 with
                | (rank1,hd1) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_List.append out tl), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_List.append out (m :: tl)), rank1))
                    else
                      (let uu____9360 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9365 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9365)
                          in
                       if uu____9360
                       then
                         match min with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), out) tl
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), (m ::
                                 out)) tl
                       else aux (min_rank, min, (hd1 :: out)) tl)))
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
          let uu____9438 = FStar_Syntax_Util.head_and_args t  in
          match uu____9438 with
          | (hd,uu____9457) ->
              let uu____9482 =
                let uu____9483 = FStar_Syntax_Subst.compress hd  in
                uu____9483.FStar_Syntax_Syntax.n  in
              (match uu____9482 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9488) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9523  ->
                           match uu____9523 with
                           | (y,uu____9532) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9555  ->
                                       match uu____9555 with
                                       | (x,uu____9564) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9569 -> false)
           in
        let uu____9571 = rank tcenv p  in
        match uu____9571 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9580 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9661 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9680 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9699 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9716 = FStar_Thunk.mkv s  in UFailed uu____9716 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9731 = mklstr s  in UFailed uu____9731 
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
                        let uu____9782 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9782 with
                        | (k,uu____9790) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9805 -> false)))
            | uu____9807 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9859 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  FStar_Syntax_Util.eq_univs uv1 uv2))
                           in
                        if uu____9859 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____9883 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  -> FStar_Syntax_Util.eq_univs u u'))
                      in
                   Prims.op_Negation uu____9883)
               in
            let uu____9890 = filter u12  in
            let uu____9893 = filter u22  in (uu____9890, uu____9893)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9928 = filter_out_common_univs us1 us2  in
                   (match uu____9928 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9988 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9988 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9991 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10008  ->
                               let uu____10009 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10011 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10009 uu____10011))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10037 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10037 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10063 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10063 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10066 ->
                   ufailed_thunk
                     (fun uu____10077  ->
                        let uu____10078 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10080 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10078 uu____10080 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10083,uu____10084) ->
              let uu____10086 =
                let uu____10088 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10090 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10088 uu____10090
                 in
              failwith uu____10086
          | (FStar_Syntax_Syntax.U_unknown ,uu____10093) ->
              let uu____10094 =
                let uu____10096 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10098 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10096 uu____10098
                 in
              failwith uu____10094
          | (uu____10101,FStar_Syntax_Syntax.U_bvar uu____10102) ->
              let uu____10104 =
                let uu____10106 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10108 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10106 uu____10108
                 in
              failwith uu____10104
          | (uu____10111,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10112 =
                let uu____10114 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10116 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10114 uu____10116
                 in
              failwith uu____10112
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10121 =
                let uu____10123 = FStar_Ident.text_of_id x  in
                let uu____10125 = FStar_Ident.text_of_id y  in
                uu____10123 = uu____10125  in
              if uu____10121
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10156 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10156
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10175 = occurs_univ v1 u3  in
              if uu____10175
              then
                let uu____10178 =
                  let uu____10180 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10182 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10180 uu____10182
                   in
                try_umax_components u11 u21 uu____10178
              else
                (let uu____10187 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10187)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10201 = occurs_univ v1 u3  in
              if uu____10201
              then
                let uu____10204 =
                  let uu____10206 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10208 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10206 uu____10208
                   in
                try_umax_components u11 u21 uu____10204
              else
                (let uu____10213 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10213)
          | (FStar_Syntax_Syntax.U_max uu____10214,uu____10215) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10223 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10223
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10229,FStar_Syntax_Syntax.U_max uu____10230) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10238 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10238
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10244,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10246,FStar_Syntax_Syntax.U_name uu____10247) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10249) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10251) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10253,FStar_Syntax_Syntax.U_succ uu____10254) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10256,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10363 = bc1  in
      match uu____10363 with
      | (bs1,mk_cod1) ->
          let uu____10407 = bc2  in
          (match uu____10407 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10518 = aux xs ys  in
                     (match uu____10518 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10601 =
                       let uu____10608 = mk_cod1 xs  in ([], uu____10608)  in
                     let uu____10611 =
                       let uu____10618 = mk_cod2 ys  in ([], uu____10618)  in
                     (uu____10601, uu____10611)
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
                  let uu____10687 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10687 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10690 =
                    let uu____10691 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10691 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10690
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10696 = has_type_guard t1 t2  in (uu____10696, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10697 = has_type_guard t2 t1  in (uu____10697, wl)
  
let is_flex_pat :
  'uuuuuu10707 'uuuuuu10708 'uuuuuu10709 .
    ('uuuuuu10707 * 'uuuuuu10708 * 'uuuuuu10709 Prims.list) -> Prims.bool
  =
  fun uu___22_10723  ->
    match uu___22_10723 with
    | (uu____10732,uu____10733,[]) -> true
    | uu____10737 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10770 = f  in
      match uu____10770 with
      | (uu____10777,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10778;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10779;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10782;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10783;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10784;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10785;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10857  ->
                 match uu____10857 with
                 | (y,uu____10866) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11020 =
                  let uu____11035 =
                    let uu____11038 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11038  in
                  ((FStar_List.rev pat_binders), uu____11035)  in
                FStar_Pervasives_Native.Some uu____11020
            | (uu____11071,[]) ->
                let uu____11102 =
                  let uu____11117 =
                    let uu____11120 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11120  in
                  ((FStar_List.rev pat_binders), uu____11117)  in
                FStar_Pervasives_Native.Some uu____11102
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11211 =
                  let uu____11212 = FStar_Syntax_Subst.compress a  in
                  uu____11212.FStar_Syntax_Syntax.n  in
                (match uu____11211 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11232 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11232
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1631_11262 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1631_11262.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1631_11262.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11266 =
                            let uu____11267 =
                              let uu____11274 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11274)  in
                            FStar_Syntax_Syntax.NT uu____11267  in
                          [uu____11266]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1637_11290 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1637_11290.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1637_11290.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11291 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11331 =
                  let uu____11338 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11338  in
                (match uu____11331 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11397 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11422 ->
               let uu____11423 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11423 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11719 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11719
       then
         let uu____11724 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11724
       else ());
      (let uu____11730 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11730
       then
         let uu____11735 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11735
       else ());
      (let uu____11740 = next_prob probs  in
       match uu____11740 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1664_11767 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1664_11767.wl_deferred);
               ctr = (uu___1664_11767.ctr);
               defer_ok = (uu___1664_11767.defer_ok);
               smt_ok = (uu___1664_11767.smt_ok);
               umax_heuristic_ok = (uu___1664_11767.umax_heuristic_ok);
               tcenv = (uu___1664_11767.tcenv);
               wl_implicits = (uu___1664_11767.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11776 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11776
                 then
                   let uu____11779 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____11779
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
                       (let uu____11786 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd
                            probs1
                           in
                        solve env uu____11786)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1676_11792 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1676_11792.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1676_11792.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1676_11792.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1676_11792.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1676_11792.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1676_11792.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1676_11792.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1676_11792.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1676_11792.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11817 ->
                let uu____11827 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11892  ->
                          match uu____11892 with
                          | (c,uu____11902,uu____11903) -> c < probs.ctr))
                   in
                (match uu____11827 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11951 =
                            let uu____11956 =
                              FStar_List.map
                                (fun uu____11977  ->
                                   match uu____11977 with
                                   | (uu____11993,x,y) ->
                                       let uu____12004 = FStar_Thunk.force x
                                          in
                                       (uu____12004, y)) probs.wl_deferred
                               in
                            (uu____11956, (probs.wl_implicits))  in
                          Success uu____11951
                      | uu____12008 ->
                          let uu____12018 =
                            let uu___1694_12019 = probs  in
                            let uu____12020 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12041  ->
                                      match uu____12041 with
                                      | (uu____12049,uu____12050,y) -> y))
                               in
                            {
                              attempting = uu____12020;
                              wl_deferred = rest;
                              ctr = (uu___1694_12019.ctr);
                              defer_ok = (uu___1694_12019.defer_ok);
                              smt_ok = (uu___1694_12019.smt_ok);
                              umax_heuristic_ok =
                                (uu___1694_12019.umax_heuristic_ok);
                              tcenv = (uu___1694_12019.tcenv);
                              wl_implicits = (uu___1694_12019.wl_implicits)
                            }  in
                          solve env uu____12018))))

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
            let uu____12059 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12059 with
            | USolved wl1 ->
                let uu____12061 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12061
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12064 = defer_lit "" orig wl1  in
                solve env uu____12064

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
                  let uu____12115 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12115 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12118 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12131;
                  FStar_Syntax_Syntax.vars = uu____12132;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12135;
                  FStar_Syntax_Syntax.vars = uu____12136;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12149,uu____12150) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12158,FStar_Syntax_Syntax.Tm_uinst uu____12159) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12167 -> USolved wl

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
            ((let uu____12178 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12178
              then
                let uu____12183 = prob_to_string env orig  in
                let uu____12185 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12183 uu____12185
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
               let uu____12278 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12278 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12333 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12333
                then
                  let uu____12338 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12340 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12338 uu____12340
                else ());
               (let uu____12345 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12345 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12391 = eq_prob t1 t2 wl2  in
                         (match uu____12391 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12412 ->
                         let uu____12421 = eq_prob t1 t2 wl2  in
                         (match uu____12421 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12471 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12486 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12487 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12486, uu____12487)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12492 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12493 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12492, uu____12493)
                            in
                         (match uu____12471 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12524 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12524 with
                                | (t1_hd,t1_args) ->
                                    let uu____12569 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12569 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12635 =
                                              let uu____12642 =
                                                let uu____12653 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12653 :: t1_args  in
                                              let uu____12670 =
                                                let uu____12679 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12679 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12728  ->
                                                   fun uu____12729  ->
                                                     fun uu____12730  ->
                                                       match (uu____12728,
                                                               uu____12729,
                                                               uu____12730)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12780),
                                                          (a2,uu____12782))
                                                           ->
                                                           let uu____12819 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12819
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12642
                                                uu____12670
                                               in
                                            match uu____12635 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1848_12845 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1848_12845.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1848_12845.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1848_12845.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12856 =
                                                  solve env1 wl'  in
                                                (match uu____12856 with
                                                 | Success (uu____12859,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1857_12863
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1857_12863.attempting);
                                                            wl_deferred =
                                                              (uu___1857_12863.wl_deferred);
                                                            ctr =
                                                              (uu___1857_12863.ctr);
                                                            defer_ok =
                                                              (uu___1857_12863.defer_ok);
                                                            smt_ok =
                                                              (uu___1857_12863.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1857_12863.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1857_12863.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12864 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12896 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12896 with
                                | (t1_base,p1_opt) ->
                                    let uu____12932 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12932 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13031 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13031
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
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi2
                                                  in
                                               let uu____13084 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13084
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi
                                                  in
                                               let uu____13116 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13116
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi
                                                  in
                                               let uu____13148 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13148
                                           | uu____13151 -> t_base  in
                                         let uu____13168 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13168 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13182 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13182, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13189 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13189 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13225 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13225 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13261 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13261
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
                              let uu____13285 = combine t11 t21 wl2  in
                              (match uu____13285 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13318 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13318
                                     then
                                       let uu____13323 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13323
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13365 ts1 =
               match uu____13365 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13428 = pairwise out t wl2  in
                        (match uu____13428 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13464 =
               let uu____13475 = FStar_List.hd ts  in (uu____13475, [], wl1)
                in
             let uu____13484 = FStar_List.tl ts  in
             aux uu____13464 uu____13484  in
           let uu____13491 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13491 with
           | (this_flex,this_rigid) ->
               let uu____13517 =
                 let uu____13518 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13518.FStar_Syntax_Syntax.n  in
               (match uu____13517 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13543 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13543
                    then
                      let uu____13546 = destruct_flex_t this_flex wl  in
                      (match uu____13546 with
                       | (flex,wl1) ->
                           let uu____13553 = quasi_pattern env flex  in
                           (match uu____13553 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____13572 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13572
                                  then
                                    let uu____13577 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13577
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13584 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1959_13587 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1959_13587.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1959_13587.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1959_13587.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1959_13587.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1959_13587.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1959_13587.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1959_13587.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1959_13587.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1959_13587.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13584)
                | uu____13588 ->
                    ((let uu____13590 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13590
                      then
                        let uu____13595 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13595
                      else ());
                     (let uu____13600 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13600 with
                      | (u,_args) ->
                          let uu____13643 =
                            let uu____13644 = FStar_Syntax_Subst.compress u
                               in
                            uu____13644.FStar_Syntax_Syntax.n  in
                          (match uu____13643 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____13672 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13672 with
                                 | (u',uu____13691) ->
                                     let uu____13716 =
                                       let uu____13717 = whnf env u'  in
                                       uu____13717.FStar_Syntax_Syntax.n  in
                                     (match uu____13716 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13739 -> false)
                                  in
                               let uu____13741 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13764  ->
                                         match uu___23_13764 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____13778 -> false)
                                         | uu____13782 -> false))
                                  in
                               (match uu____13741 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13797 = whnf env this_rigid
                                         in
                                      let uu____13798 =
                                        FStar_List.collect
                                          (fun uu___24_13804  ->
                                             match uu___24_13804 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13810 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13810]
                                             | uu____13814 -> [])
                                          bounds_probs
                                         in
                                      uu____13797 :: uu____13798  in
                                    let uu____13815 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13815 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13848 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13863 =
                                               let uu____13864 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13864.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13863 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13876 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13876)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13887 -> bound  in
                                           let uu____13888 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13888)  in
                                         (match uu____13848 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13923 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13923
                                                then
                                                  let wl'1 =
                                                    let uu___2019_13929 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2019_13929.wl_deferred);
                                                      ctr =
                                                        (uu___2019_13929.ctr);
                                                      defer_ok =
                                                        (uu___2019_13929.defer_ok);
                                                      smt_ok =
                                                        (uu___2019_13929.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2019_13929.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2019_13929.tcenv);
                                                      wl_implicits =
                                                        (uu___2019_13929.wl_implicits)
                                                    }  in
                                                  let uu____13930 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13930
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13936 =
                                                  solve_t env eq_prob
                                                    (let uu___2024_13938 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2024_13938.wl_deferred);
                                                       ctr =
                                                         (uu___2024_13938.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2024_13938.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2024_13938.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2024_13938.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13936 with
                                                | Success (uu____13940,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2030_13943 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2030_13943.wl_deferred);
                                                        ctr =
                                                          (uu___2030_13943.ctr);
                                                        defer_ok =
                                                          (uu___2030_13943.defer_ok);
                                                        smt_ok =
                                                          (uu___2030_13943.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2030_13943.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2030_13943.tcenv);
                                                        wl_implicits =
                                                          (uu___2030_13943.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2033_13945 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2033_13945.attempting);
                                                        wl_deferred =
                                                          (uu___2033_13945.wl_deferred);
                                                        ctr =
                                                          (uu___2033_13945.ctr);
                                                        defer_ok =
                                                          (uu___2033_13945.defer_ok);
                                                        smt_ok =
                                                          (uu___2033_13945.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2033_13945.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2033_13945.tcenv);
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
                                                    let uu____13961 =
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
                                                    ((let uu____13973 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13973
                                                      then
                                                        let uu____13978 =
                                                          let uu____13980 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13980
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13978
                                                      else ());
                                                     (let uu____13993 =
                                                        let uu____14008 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14008)
                                                         in
                                                      match uu____13993 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14030))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14056 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14056
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
                                                                  let uu____14076
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14076))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14101 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14101
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
                                                                    let uu____14121
                                                                    =
                                                                    let uu____14126
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14126
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14121
                                                                    [] wl2
                                                                     in
                                                                  let uu____14132
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14132))))
                                                      | uu____14133 ->
                                                          let uu____14148 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14148 p)))))))
                           | uu____14155 when flip ->
                               let uu____14156 =
                                 let uu____14158 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14160 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14158 uu____14160
                                  in
                               failwith uu____14156
                           | uu____14163 ->
                               let uu____14164 =
                                 let uu____14166 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14168 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14166 uu____14168
                                  in
                               failwith uu____14164)))))

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
                fun arrow  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____14204  ->
                         match uu____14204 with
                         | (x,i) ->
                             let uu____14223 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14223, i)) bs_lhs
                     in
                  let uu____14226 = lhs  in
                  match uu____14226 with
                  | (uu____14227,u_lhs,uu____14229) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14326 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14336 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14336, univ)
                             in
                          match uu____14326 with
                          | (k,univ) ->
                              let uu____14343 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14343 with
                               | (uu____14360,u,wl3) ->
                                   let uu____14363 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14363, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14389 =
                              let uu____14402 =
                                let uu____14413 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14413 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14464  ->
                                   fun uu____14465  ->
                                     match (uu____14464, uu____14465) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14566 =
                                           let uu____14573 =
                                             let uu____14576 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14576
                                              in
                                           copy_uvar u_lhs [] uu____14573 wl2
                                            in
                                         (match uu____14566 with
                                          | (uu____14605,t_a,wl3) ->
                                              let uu____14608 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14608 with
                                               | (uu____14627,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14402
                                ([], wl1)
                               in
                            (match uu____14389 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2144_14683 = ct  in
                                   let uu____14684 =
                                     let uu____14687 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14687
                                      in
                                   let uu____14702 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2144_14683.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2144_14683.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14684;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14702;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2144_14683.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2147_14720 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2147_14720.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2147_14720.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14723 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____14723 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14761 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14761 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14772 =
                                          let uu____14777 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14777)  in
                                        TERM uu____14772  in
                                      let uu____14778 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14778 with
                                       | (sub_prob,wl3) ->
                                           let uu____14792 =
                                             let uu____14793 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14793
                                              in
                                           solve env uu____14792))
                             | (x,imp)::formals2 ->
                                 let uu____14815 =
                                   let uu____14822 =
                                     let uu____14825 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14825
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14822 wl1
                                    in
                                 (match uu____14815 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14846 =
                                          let uu____14849 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14849
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14846 u_x
                                         in
                                      let uu____14850 =
                                        let uu____14853 =
                                          let uu____14856 =
                                            let uu____14857 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14857, imp)  in
                                          [uu____14856]  in
                                        FStar_List.append bs_terms
                                          uu____14853
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14850 formals2 wl2)
                              in
                           let uu____14884 = occurs_check u_lhs arrow  in
                           (match uu____14884 with
                            | (uu____14897,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14913 =
                                    mklstr
                                      (fun uu____14918  ->
                                         let uu____14919 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14919)
                                     in
                                  giveup_or_defer env orig wl uu____14913
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
              (let uu____14952 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14952
               then
                 let uu____14957 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14960 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14957 (rel_to_string (p_rel orig)) uu____14960
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15091 = rhs wl1 scope env1 subst  in
                     (match uu____15091 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15114 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15114
                            then
                              let uu____15119 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15119
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15197 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15197 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2217_15199 = hd1  in
                       let uu____15200 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2217_15199.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2217_15199.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15200
                       }  in
                     let hd21 =
                       let uu___2220_15204 = hd2  in
                       let uu____15205 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2220_15204.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2220_15204.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15205
                       }  in
                     let uu____15208 =
                       let uu____15213 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15213
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15208 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15236 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15236
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15243 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15243 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15315 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15315
                                  in
                               ((let uu____15333 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15333
                                 then
                                   let uu____15338 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15340 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15338
                                     uu____15340
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15375 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15411 = aux wl [] env [] bs1 bs2  in
               match uu____15411 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15470 = attempt sub_probs wl2  in
                   solve env1 uu____15470)

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
            let uu___2258_15490 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2258_15490.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2258_15490.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15502 = try_solve env wl'  in
          match uu____15502 with
          | Success (uu____15503,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2267_15507 = wl  in
                  {
                    attempting = (uu___2267_15507.attempting);
                    wl_deferred = (uu___2267_15507.wl_deferred);
                    ctr = (uu___2267_15507.ctr);
                    defer_ok = (uu___2267_15507.defer_ok);
                    smt_ok = (uu___2267_15507.smt_ok);
                    umax_heuristic_ok = (uu___2267_15507.umax_heuristic_ok);
                    tcenv = (uu___2267_15507.tcenv);
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
        (let uu____15516 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15516 wl)

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
              let uu____15530 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15530 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15564 = lhs1  in
              match uu____15564 with
              | (uu____15567,ctx_u,uu____15569) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15577 ->
                        let uu____15578 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15578 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15627 = quasi_pattern env1 lhs1  in
              match uu____15627 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15661) ->
                  let uu____15666 = lhs1  in
                  (match uu____15666 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15681 = occurs_check ctx_u rhs1  in
                       (match uu____15681 with
                        | (uvars,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15732 =
                                let uu____15740 =
                                  let uu____15742 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15742
                                   in
                                FStar_Util.Inl uu____15740  in
                              (uu____15732, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15770 =
                                 let uu____15772 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15772  in
                               if uu____15770
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15799 =
                                    let uu____15807 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15807  in
                                  let uu____15813 =
                                    restrict_all_uvars ctx_u uvars wl1  in
                                  (uu____15799, uu____15813)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15857 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15857 with
              | (rhs_hd,args) ->
                  let uu____15900 = FStar_Util.prefix args  in
                  (match uu____15900 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15972 = lhs1  in
                       (match uu____15972 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15976 =
                              let uu____15987 =
                                let uu____15994 =
                                  let uu____15997 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15997
                                   in
                                copy_uvar u_lhs [] uu____15994 wl1  in
                              match uu____15987 with
                              | (uu____16024,t_last_arg,wl2) ->
                                  let uu____16027 =
                                    let uu____16034 =
                                      let uu____16035 =
                                        let uu____16044 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16044]  in
                                      FStar_List.append bs_lhs uu____16035
                                       in
                                    copy_uvar u_lhs uu____16034 t_res_lhs wl2
                                     in
                                  (match uu____16027 with
                                   | (uu____16079,lhs',wl3) ->
                                       let uu____16082 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16082 with
                                        | (uu____16099,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15976 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16120 =
                                     let uu____16121 =
                                       let uu____16126 =
                                         let uu____16127 =
                                           let uu____16130 =
                                             let uu____16135 =
                                               let uu____16136 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16136]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16135
                                              in
                                           uu____16130
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16127
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16126)  in
                                     TERM uu____16121  in
                                   [uu____16120]  in
                                 let uu____16161 =
                                   let uu____16168 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16168 with
                                   | (p1,wl3) ->
                                       let uu____16188 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16188 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16161 with
                                  | (sub_probs,wl3) ->
                                      let uu____16220 =
                                        let uu____16221 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16221  in
                                      solve env1 uu____16220))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16255 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16255 with
                | (uu____16273,args) ->
                    (match args with | [] -> false | uu____16309 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16328 =
                  let uu____16329 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16329.FStar_Syntax_Syntax.n  in
                match uu____16328 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16333 -> true
                | uu____16349 -> false  in
              let uu____16351 = quasi_pattern env1 lhs1  in
              match uu____16351 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16370  ->
                         let uu____16371 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16371)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16380 = is_app rhs1  in
                  if uu____16380
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16385 = is_arrow rhs1  in
                     if uu____16385
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16398  ->
                               let uu____16399 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16399)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16403 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16403
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16409 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16409
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16414 = lhs  in
                (match uu____16414 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16418 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16418 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16436 =
                              let uu____16440 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16440
                               in
                            FStar_All.pipe_right uu____16436
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16461 = occurs_check ctx_uv rhs1  in
                          (match uu____16461 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16490 =
                                   let uu____16491 =
                                     let uu____16493 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16493
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16491
                                    in
                                 giveup_or_defer env orig wl uu____16490
                               else
                                 (let uu____16501 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16501
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars wl  in
                                    let uu____16508 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16508
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16524  ->
                                              let uu____16525 =
                                                names_to_string1 fvs2  in
                                              let uu____16527 =
                                                names_to_string1 fvs1  in
                                              let uu____16529 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16525 uu____16527
                                                uu____16529)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16541 ->
                          if wl.defer_ok
                          then
                            let uu____16545 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16545
                          else
                            (let uu____16550 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16550 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16576 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16576
                             | (FStar_Util.Inl msg,uu____16578) ->
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
                  let uu____16596 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16596
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16602 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16602
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16624 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16624
                else
                  (let uu____16629 =
                     let uu____16646 = quasi_pattern env lhs  in
                     let uu____16653 = quasi_pattern env rhs  in
                     (uu____16646, uu____16653)  in
                   match uu____16629 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16696 = lhs  in
                       (match uu____16696 with
                        | ({ FStar_Syntax_Syntax.n = uu____16697;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16699;_},u_lhs,uu____16701)
                            ->
                            let uu____16704 = rhs  in
                            (match uu____16704 with
                             | (uu____16705,u_rhs,uu____16707) ->
                                 let uu____16708 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16708
                                 then
                                   let uu____16715 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16715
                                 else
                                   (let uu____16718 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16718 with
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
                                        let uu____16750 =
                                          let uu____16757 =
                                            let uu____16760 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16760
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16757
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16750 with
                                         | (uu____16772,w,wl1) ->
                                             let w_app =
                                               let uu____16778 =
                                                 let uu____16783 =
                                                   FStar_List.map
                                                     (fun uu____16794  ->
                                                        match uu____16794
                                                        with
                                                        | (z,uu____16802) ->
                                                            let uu____16807 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16807) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16783
                                                  in
                                               uu____16778
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16809 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16809
                                               then
                                                 let uu____16814 =
                                                   let uu____16818 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16820 =
                                                     let uu____16824 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16826 =
                                                       let uu____16830 =
                                                         term_to_string w  in
                                                       let uu____16832 =
                                                         let uu____16836 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16845 =
                                                           let uu____16849 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16858 =
                                                             let uu____16862
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16862]
                                                              in
                                                           uu____16849 ::
                                                             uu____16858
                                                            in
                                                         uu____16836 ::
                                                           uu____16845
                                                          in
                                                       uu____16830 ::
                                                         uu____16832
                                                        in
                                                     uu____16824 ::
                                                       uu____16826
                                                      in
                                                   uu____16818 :: uu____16820
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16814
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16879 =
                                                     let uu____16884 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16884)  in
                                                   TERM uu____16879  in
                                                 let uu____16885 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16885
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16893 =
                                                        let uu____16898 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16898)
                                                         in
                                                      TERM uu____16893  in
                                                    [s1; s2])
                                                  in
                                               let uu____16899 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16899))))))
                   | uu____16900 ->
                       let uu____16917 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16917)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16971 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16971
            then
              let uu____16976 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16978 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16980 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16982 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16976 uu____16978 uu____16980 uu____16982
            else ());
           (let uu____16993 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16993 with
            | (head1,args1) ->
                let uu____17036 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17036 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17106 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17106 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17111 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17111)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17132 =
                         mklstr
                           (fun uu____17143  ->
                              let uu____17144 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17146 = args_to_string args1  in
                              let uu____17150 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17152 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17144 uu____17146 uu____17150
                                uu____17152)
                          in
                       giveup env1 uu____17132 orig
                     else
                       (let uu____17159 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17164 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17164 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17159
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2523_17168 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2523_17168.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2523_17168.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2523_17168.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2523_17168.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2523_17168.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2523_17168.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2523_17168.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2523_17168.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17178 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17178
                                    else solve env1 wl2))
                        else
                          (let uu____17183 = base_and_refinement env1 t1  in
                           match uu____17183 with
                           | (base1,refinement1) ->
                               let uu____17208 = base_and_refinement env1 t2
                                  in
                               (match uu____17208 with
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
                                           let uu____17373 =
                                             FStar_List.fold_right
                                               (fun uu____17413  ->
                                                  fun uu____17414  ->
                                                    match (uu____17413,
                                                            uu____17414)
                                                    with
                                                    | (((a1,uu____17466),
                                                        (a2,uu____17468)),
                                                       (probs,wl3)) ->
                                                        let uu____17517 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17517
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17373 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17560 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17560
                                                 then
                                                   let uu____17565 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17565
                                                 else ());
                                                (let uu____17571 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17571
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
                                                    (let uu____17598 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17598 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17614 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17614
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17622 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17622))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17647 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17647 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17663 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17663
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17671 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17671)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17699 =
                                           match uu____17699 with
                                           | (prob,reason) ->
                                               ((let uu____17716 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17716
                                                 then
                                                   let uu____17721 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17723 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17721 uu____17723
                                                 else ());
                                                (let uu____17729 =
                                                   let uu____17738 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17741 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17738, uu____17741)
                                                    in
                                                 match uu____17729 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17754 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17754 with
                                                      | (head1',uu____17772)
                                                          ->
                                                          let uu____17797 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17797
                                                           with
                                                           | (head2',uu____17815)
                                                               ->
                                                               let uu____17840
                                                                 =
                                                                 let uu____17845
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17846
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17845,
                                                                   uu____17846)
                                                                  in
                                                               (match uu____17840
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17848
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17848
                                                                    then
                                                                    let uu____17853
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17855
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17857
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17859
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17853
                                                                    uu____17855
                                                                    uu____17857
                                                                    uu____17859
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17864
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2611_17872
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2611_17872.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2611_17872.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2611_17872.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2611_17872.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2611_17872.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2611_17872.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2611_17872.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2611_17872.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17874
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17874
                                                                    then
                                                                    let uu____17879
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17879
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17884 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17896 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17896 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17904 =
                                             let uu____17905 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17905.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17904 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17910 -> false  in
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
                                          | uu____17913 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17916 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2631_17952 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2631_17952.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2631_17952.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2631_17952.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2631_17952.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2631_17952.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2631_17952.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2631_17952.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2631_17952.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18028 = destruct_flex_t scrutinee wl1  in
             match uu____18028 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18039 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18039 with
                  | (xs,pat_term,uu____18055,uu____18056) ->
                      let uu____18061 =
                        FStar_List.fold_left
                          (fun uu____18084  ->
                             fun x  ->
                               match uu____18084 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18105 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18105 with
                                    | (uu____18124,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18061 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18145 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18145 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2671_18162 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2671_18162.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2671_18162.umax_heuristic_ok);
                                    tcenv = (uu___2671_18162.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18173 = solve env1 wl'  in
                                (match uu____18173 with
                                 | Success (uu____18176,imps) ->
                                     let wl'1 =
                                       let uu___2679_18179 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2679_18179.wl_deferred);
                                         ctr = (uu___2679_18179.ctr);
                                         defer_ok =
                                           (uu___2679_18179.defer_ok);
                                         smt_ok = (uu___2679_18179.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2679_18179.umax_heuristic_ok);
                                         tcenv = (uu___2679_18179.tcenv);
                                         wl_implicits =
                                           (uu___2679_18179.wl_implicits)
                                       }  in
                                     let uu____18180 = solve env1 wl'1  in
                                     (match uu____18180 with
                                      | Success (uu____18183,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2687_18187 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2687_18187.attempting);
                                                 wl_deferred =
                                                   (uu___2687_18187.wl_deferred);
                                                 ctr = (uu___2687_18187.ctr);
                                                 defer_ok =
                                                   (uu___2687_18187.defer_ok);
                                                 smt_ok =
                                                   (uu___2687_18187.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2687_18187.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2687_18187.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18188 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18194 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18217 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18217
                 then
                   let uu____18222 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18224 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18222 uu____18224
                 else ());
                (let uu____18229 =
                   let uu____18250 =
                     let uu____18259 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18259)  in
                   let uu____18266 =
                     let uu____18275 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18275)  in
                   (uu____18250, uu____18266)  in
                 match uu____18229 with
                 | ((uu____18305,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18308;
                                   FStar_Syntax_Syntax.vars = uu____18309;_}),
                    (s,t)) ->
                     let uu____18380 =
                       let uu____18382 = is_flex scrutinee  in
                       Prims.op_Negation uu____18382  in
                     if uu____18380
                     then
                       ((let uu____18393 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18393
                         then
                           let uu____18398 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18398
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18417 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18417
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18432 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18432
                           then
                             let uu____18437 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18439 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18437 uu____18439
                           else ());
                          (let pat_discriminates uu___25_18464 =
                             match uu___25_18464 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18480;
                                  FStar_Syntax_Syntax.p = uu____18481;_},FStar_Pervasives_Native.None
                                ,uu____18482) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18496;
                                  FStar_Syntax_Syntax.p = uu____18497;_},FStar_Pervasives_Native.None
                                ,uu____18498) -> true
                             | uu____18525 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18628 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18628 with
                                       | (uu____18630,uu____18631,t') ->
                                           let uu____18649 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18649 with
                                            | (FullMatch ,uu____18661) ->
                                                true
                                            | (HeadMatch
                                               uu____18675,uu____18676) ->
                                                true
                                            | uu____18691 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18728 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18728
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18739 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18739 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18827,uu____18828) ->
                                       branches1
                                   | uu____18973 -> branches  in
                                 let uu____19028 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19037 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19037 with
                                        | (p,uu____19041,uu____19042) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19071  ->
                                      FStar_Util.Inr uu____19071) uu____19028))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19101 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19101 with
                                | (p,uu____19110,e) ->
                                    ((let uu____19129 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19129
                                      then
                                        let uu____19134 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19136 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19134 uu____19136
                                      else ());
                                     (let uu____19141 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19156  ->
                                           FStar_Util.Inr uu____19156)
                                        uu____19141)))))
                 | ((s,t),(uu____19159,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19162;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19163;_}))
                     ->
                     let uu____19232 =
                       let uu____19234 = is_flex scrutinee  in
                       Prims.op_Negation uu____19234  in
                     if uu____19232
                     then
                       ((let uu____19245 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19245
                         then
                           let uu____19250 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19250
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19269 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19269
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19284 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19284
                           then
                             let uu____19289 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19291 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19289 uu____19291
                           else ());
                          (let pat_discriminates uu___25_19316 =
                             match uu___25_19316 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19332;
                                  FStar_Syntax_Syntax.p = uu____19333;_},FStar_Pervasives_Native.None
                                ,uu____19334) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19348;
                                  FStar_Syntax_Syntax.p = uu____19349;_},FStar_Pervasives_Native.None
                                ,uu____19350) -> true
                             | uu____19377 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19480 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19480 with
                                       | (uu____19482,uu____19483,t') ->
                                           let uu____19501 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19501 with
                                            | (FullMatch ,uu____19513) ->
                                                true
                                            | (HeadMatch
                                               uu____19527,uu____19528) ->
                                                true
                                            | uu____19543 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19580 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19580
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19591 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19591 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19679,uu____19680) ->
                                       branches1
                                   | uu____19825 -> branches  in
                                 let uu____19880 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19889 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19889 with
                                        | (p,uu____19893,uu____19894) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19923  ->
                                      FStar_Util.Inr uu____19923) uu____19880))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19953 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19953 with
                                | (p,uu____19962,e) ->
                                    ((let uu____19981 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19981
                                      then
                                        let uu____19986 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19988 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19986 uu____19988
                                      else ());
                                     (let uu____19993 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20008  ->
                                           FStar_Util.Inr uu____20008)
                                        uu____19993)))))
                 | uu____20009 ->
                     ((let uu____20031 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20031
                       then
                         let uu____20036 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20038 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20036 uu____20038
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20084 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20084
            then
              let uu____20089 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20091 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20093 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20095 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20089 uu____20091 uu____20093 uu____20095
            else ());
           (let uu____20100 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20100 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20131,uu____20132) ->
                     let rec may_relate head =
                       let uu____20160 =
                         let uu____20161 = FStar_Syntax_Subst.compress head
                            in
                         uu____20161.FStar_Syntax_Syntax.n  in
                       match uu____20160 with
                       | FStar_Syntax_Syntax.Tm_name uu____20165 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20167 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20192 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20192 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20194 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20197
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20198 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20201,uu____20202) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20244) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20250) ->
                           may_relate t
                       | uu____20255 -> false  in
                     let uu____20257 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20257 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20270 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20270
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20280 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20280
                          then
                            let uu____20283 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20283 with
                             | (guard,wl2) ->
                                 let uu____20290 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20290)
                          else
                            (let uu____20293 =
                               mklstr
                                 (fun uu____20304  ->
                                    let uu____20305 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20307 =
                                      let uu____20309 =
                                        let uu____20313 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20313
                                          (fun x  ->
                                             let uu____20320 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20320)
                                         in
                                      FStar_Util.dflt "" uu____20309  in
                                    let uu____20325 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20327 =
                                      let uu____20329 =
                                        let uu____20333 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20333
                                          (fun x  ->
                                             let uu____20340 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20340)
                                         in
                                      FStar_Util.dflt "" uu____20329  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20305 uu____20307 uu____20325
                                      uu____20327)
                                in
                             giveup env1 uu____20293 orig))
                 | (HeadMatch (true ),uu____20346) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20361 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20361 with
                        | (guard,wl2) ->
                            let uu____20368 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20368)
                     else
                       (let uu____20371 =
                          mklstr
                            (fun uu____20378  ->
                               let uu____20379 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20381 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20379 uu____20381)
                           in
                        giveup env1 uu____20371 orig)
                 | (uu____20384,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2862_20398 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2862_20398.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2862_20398.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2862_20398.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2862_20398.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2862_20398.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2862_20398.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2862_20398.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2862_20398.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20425 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20425
          then
            let uu____20428 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20428
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20434 =
                let uu____20437 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20437  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20434 t1);
             (let uu____20456 =
                let uu____20459 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20459  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20456 t2);
             (let uu____20478 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20478
              then
                let uu____20482 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20484 =
                  let uu____20486 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20488 =
                    let uu____20490 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20490  in
                  Prims.op_Hat uu____20486 uu____20488  in
                let uu____20493 =
                  let uu____20495 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20497 =
                    let uu____20499 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20499  in
                  Prims.op_Hat uu____20495 uu____20497  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20482 uu____20484 uu____20493
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20506,uu____20507) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20523,FStar_Syntax_Syntax.Tm_delayed uu____20524) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20540,uu____20541) ->
                  let uu____20568 =
                    let uu___2893_20569 = problem  in
                    let uu____20570 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2893_20569.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20570;
                      FStar_TypeChecker_Common.relation =
                        (uu___2893_20569.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2893_20569.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2893_20569.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2893_20569.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2893_20569.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2893_20569.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2893_20569.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2893_20569.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20568 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20571,uu____20572) ->
                  let uu____20579 =
                    let uu___2899_20580 = problem  in
                    let uu____20581 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2899_20580.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20581;
                      FStar_TypeChecker_Common.relation =
                        (uu___2899_20580.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2899_20580.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2899_20580.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2899_20580.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2899_20580.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2899_20580.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2899_20580.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2899_20580.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20579 wl
              | (uu____20582,FStar_Syntax_Syntax.Tm_ascribed uu____20583) ->
                  let uu____20610 =
                    let uu___2905_20611 = problem  in
                    let uu____20612 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2905_20611.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2905_20611.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2905_20611.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20612;
                      FStar_TypeChecker_Common.element =
                        (uu___2905_20611.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2905_20611.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2905_20611.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2905_20611.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2905_20611.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2905_20611.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20610 wl
              | (uu____20613,FStar_Syntax_Syntax.Tm_meta uu____20614) ->
                  let uu____20621 =
                    let uu___2911_20622 = problem  in
                    let uu____20623 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2911_20622.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2911_20622.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2911_20622.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20623;
                      FStar_TypeChecker_Common.element =
                        (uu___2911_20622.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2911_20622.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2911_20622.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2911_20622.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2911_20622.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2911_20622.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20621 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20625),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20627)) ->
                  let uu____20636 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20636
              | (FStar_Syntax_Syntax.Tm_bvar uu____20637,uu____20638) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20640,FStar_Syntax_Syntax.Tm_bvar uu____20641) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___26_20711 =
                    match uu___26_20711 with
                    | [] -> c
                    | bs ->
                        let uu____20739 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20739
                     in
                  let uu____20750 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20750 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst c21
                                     in
                                  let rel =
                                    let uu____20899 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20899
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
                  let mk_t t l uu___27_20988 =
                    match uu___27_20988 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21030 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21030 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21175 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21176 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21175
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21176 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21178,uu____21179) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21210 -> true
                    | uu____21230 -> false  in
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
                      (let uu____21290 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3013_21298 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3013_21298.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3013_21298.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3013_21298.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3013_21298.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3013_21298.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3013_21298.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3013_21298.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3013_21298.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3013_21298.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3013_21298.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3013_21298.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3013_21298.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3013_21298.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3013_21298.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3013_21298.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3013_21298.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3013_21298.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3013_21298.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3013_21298.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3013_21298.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3013_21298.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3013_21298.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3013_21298.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3013_21298.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3013_21298.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3013_21298.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3013_21298.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3013_21298.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3013_21298.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3013_21298.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3013_21298.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3013_21298.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3013_21298.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3013_21298.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3013_21298.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3013_21298.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3013_21298.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3013_21298.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3013_21298.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3013_21298.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3013_21298.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3013_21298.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3013_21298.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21290 with
                       | (uu____21303,ty,uu____21305) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21314 =
                                 let uu____21315 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21315.FStar_Syntax_Syntax.n  in
                               match uu____21314 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21318 ->
                                   let uu____21325 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21325
                               | uu____21326 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21329 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21329
                             then
                               let uu____21334 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21336 =
                                 let uu____21338 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21338
                                  in
                               let uu____21339 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21334 uu____21336 uu____21339
                             else ());
                            r1))
                     in
                  let uu____21344 =
                    let uu____21361 = maybe_eta t1  in
                    let uu____21368 = maybe_eta t2  in
                    (uu____21361, uu____21368)  in
                  (match uu____21344 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3034_21410 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3034_21410.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3034_21410.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3034_21410.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3034_21410.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3034_21410.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3034_21410.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3034_21410.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3034_21410.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21431 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21431
                       then
                         let uu____21434 = destruct_flex_t not_abs wl  in
                         (match uu____21434 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21451 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21451.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21451.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21451.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21451.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21451.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21451.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21451.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21451.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21454 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21454 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21477 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21477
                       then
                         let uu____21480 = destruct_flex_t not_abs wl  in
                         (match uu____21480 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21497 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21497.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21497.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21497.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21497.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21497.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21497.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21497.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21497.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21500 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21500 orig))
                   | uu____21503 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21521,FStar_Syntax_Syntax.Tm_abs uu____21522) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21553 -> true
                    | uu____21573 -> false  in
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
                      (let uu____21633 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3013_21641 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3013_21641.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3013_21641.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3013_21641.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3013_21641.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3013_21641.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3013_21641.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3013_21641.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3013_21641.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3013_21641.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3013_21641.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3013_21641.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3013_21641.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3013_21641.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3013_21641.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3013_21641.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3013_21641.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3013_21641.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3013_21641.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3013_21641.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3013_21641.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3013_21641.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3013_21641.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3013_21641.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3013_21641.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3013_21641.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3013_21641.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3013_21641.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3013_21641.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3013_21641.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3013_21641.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3013_21641.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3013_21641.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3013_21641.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3013_21641.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3013_21641.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3013_21641.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3013_21641.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3013_21641.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3013_21641.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3013_21641.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3013_21641.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3013_21641.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3013_21641.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21633 with
                       | (uu____21646,ty,uu____21648) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21657 =
                                 let uu____21658 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21658.FStar_Syntax_Syntax.n  in
                               match uu____21657 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21661 ->
                                   let uu____21668 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21668
                               | uu____21669 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21672 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21672
                             then
                               let uu____21677 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21679 =
                                 let uu____21681 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21681
                                  in
                               let uu____21682 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21677 uu____21679 uu____21682
                             else ());
                            r1))
                     in
                  let uu____21687 =
                    let uu____21704 = maybe_eta t1  in
                    let uu____21711 = maybe_eta t2  in
                    (uu____21704, uu____21711)  in
                  (match uu____21687 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3034_21753 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3034_21753.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3034_21753.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3034_21753.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3034_21753.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3034_21753.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3034_21753.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3034_21753.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3034_21753.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21774 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21774
                       then
                         let uu____21777 = destruct_flex_t not_abs wl  in
                         (match uu____21777 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21794 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21794.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21794.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21794.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21794.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21794.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21794.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21794.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21794.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21797 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21797 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21820 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21820
                       then
                         let uu____21823 = destruct_flex_t not_abs wl  in
                         (match uu____21823 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21840 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21840.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21840.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21840.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21840.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21840.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21840.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21840.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21840.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21843 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21843 orig))
                   | uu____21846 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21876 =
                    let uu____21881 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21881 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3074_21909 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3074_21909.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3074_21909.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3076_21911 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3076_21911.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3076_21911.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21912,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3074_21927 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3074_21927.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3074_21927.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3076_21929 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3076_21929.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3076_21929.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21930 -> (x1, x2)  in
                  (match uu____21876 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21949 = as_refinement false env t11  in
                       (match uu____21949 with
                        | (x12,phi11) ->
                            let uu____21957 = as_refinement false env t21  in
                            (match uu____21957 with
                             | (x22,phi21) ->
                                 ((let uu____21966 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21966
                                   then
                                     ((let uu____21971 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21973 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21975 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21971
                                         uu____21973 uu____21975);
                                      (let uu____21978 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21980 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21982 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21978
                                         uu____21980 uu____21982))
                                   else ());
                                  (let uu____21987 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21987 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp imp phi13 phi23 =
                                         let uu____22058 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22058
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22070 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____22083 =
                                            let uu____22086 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22086
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22083
                                            (p_guard base_prob));
                                         (let uu____22105 =
                                            let uu____22108 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22108
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22105
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22127 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22127)
                                          in
                                       let has_uvars =
                                         (let uu____22132 =
                                            let uu____22134 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22134
                                             in
                                          Prims.op_Negation uu____22132) ||
                                           (let uu____22138 =
                                              let uu____22140 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22140
                                               in
                                            Prims.op_Negation uu____22138)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22144 =
                                           let uu____22149 =
                                             let uu____22158 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22158]  in
                                           mk_t_problem wl1 uu____22149 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22144 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22181 =
                                                solve env1
                                                  (let uu___3119_22183 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3119_22183.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3119_22183.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3119_22183.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3119_22183.tcenv);
                                                     wl_implicits =
                                                       (uu___3119_22183.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22181 with
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
                                               | Success uu____22198 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22207 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22207
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3132_22216 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3132_22216.attempting);
                                                         wl_deferred =
                                                           (uu___3132_22216.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3132_22216.defer_ok);
                                                         smt_ok =
                                                           (uu___3132_22216.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3132_22216.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3132_22216.tcenv);
                                                         wl_implicits =
                                                           (uu___3132_22216.wl_implicits)
                                                       }  in
                                                     let uu____22218 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22218))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22221,FStar_Syntax_Syntax.Tm_uvar uu____22222) ->
                  let uu____22247 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22247 with
                   | (t11,wl1) ->
                       let uu____22254 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22254 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22263;
                    FStar_Syntax_Syntax.pos = uu____22264;
                    FStar_Syntax_Syntax.vars = uu____22265;_},uu____22266),FStar_Syntax_Syntax.Tm_uvar
                 uu____22267) ->
                  let uu____22316 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22316 with
                   | (t11,wl1) ->
                       let uu____22323 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22323 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22332,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22333;
                    FStar_Syntax_Syntax.pos = uu____22334;
                    FStar_Syntax_Syntax.vars = uu____22335;_},uu____22336))
                  ->
                  let uu____22385 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22385 with
                   | (t11,wl1) ->
                       let uu____22392 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22392 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22401;
                    FStar_Syntax_Syntax.pos = uu____22402;
                    FStar_Syntax_Syntax.vars = uu____22403;_},uu____22404),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22405;
                    FStar_Syntax_Syntax.pos = uu____22406;
                    FStar_Syntax_Syntax.vars = uu____22407;_},uu____22408))
                  ->
                  let uu____22481 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22481 with
                   | (t11,wl1) ->
                       let uu____22488 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22488 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22497,uu____22498) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22511 = destruct_flex_t t1 wl  in
                  (match uu____22511 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22518;
                    FStar_Syntax_Syntax.pos = uu____22519;
                    FStar_Syntax_Syntax.vars = uu____22520;_},uu____22521),uu____22522)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22559 = destruct_flex_t t1 wl  in
                  (match uu____22559 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22566,FStar_Syntax_Syntax.Tm_uvar uu____22567) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22580,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22581;
                    FStar_Syntax_Syntax.pos = uu____22582;
                    FStar_Syntax_Syntax.vars = uu____22583;_},uu____22584))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22621,FStar_Syntax_Syntax.Tm_arrow uu____22622) ->
                  solve_t' env
                    (let uu___3234_22650 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3234_22650.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3234_22650.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3234_22650.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3234_22650.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3234_22650.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3234_22650.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3234_22650.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3234_22650.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3234_22650.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22651;
                    FStar_Syntax_Syntax.pos = uu____22652;
                    FStar_Syntax_Syntax.vars = uu____22653;_},uu____22654),FStar_Syntax_Syntax.Tm_arrow
                 uu____22655) ->
                  solve_t' env
                    (let uu___3234_22707 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3234_22707.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3234_22707.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3234_22707.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3234_22707.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3234_22707.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3234_22707.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3234_22707.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3234_22707.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3234_22707.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22708,FStar_Syntax_Syntax.Tm_uvar uu____22709) ->
                  let uu____22722 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22722
              | (uu____22723,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22724;
                    FStar_Syntax_Syntax.pos = uu____22725;
                    FStar_Syntax_Syntax.vars = uu____22726;_},uu____22727))
                  ->
                  let uu____22764 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22764
              | (FStar_Syntax_Syntax.Tm_uvar uu____22765,uu____22766) ->
                  let uu____22779 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22779
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22780;
                    FStar_Syntax_Syntax.pos = uu____22781;
                    FStar_Syntax_Syntax.vars = uu____22782;_},uu____22783),uu____22784)
                  ->
                  let uu____22821 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22821
              | (FStar_Syntax_Syntax.Tm_refine uu____22822,uu____22823) ->
                  let t21 =
                    let uu____22831 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22831  in
                  solve_t env
                    (let uu___3269_22857 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3269_22857.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3269_22857.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3269_22857.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3269_22857.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3269_22857.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3269_22857.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3269_22857.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3269_22857.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3269_22857.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22858,FStar_Syntax_Syntax.Tm_refine uu____22859) ->
                  let t11 =
                    let uu____22867 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22867  in
                  solve_t env
                    (let uu___3276_22893 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3276_22893.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3276_22893.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3276_22893.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3276_22893.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3276_22893.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3276_22893.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3276_22893.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3276_22893.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3276_22893.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22975 =
                    let uu____22976 = guard_of_prob env wl problem t1 t2  in
                    match uu____22976 with
                    | (guard,wl1) ->
                        let uu____22983 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22983
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23202 = br1  in
                        (match uu____23202 with
                         | (p1,w1,uu____23231) ->
                             let uu____23248 = br2  in
                             (match uu____23248 with
                              | (p2,w2,uu____23271) ->
                                  let uu____23276 =
                                    let uu____23278 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23278  in
                                  if uu____23276
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23305 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23305 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23342 = br2  in
                                         (match uu____23342 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23375 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23375
                                                 in
                                              let uu____23380 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23411,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23432) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23491 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23491 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23380
                                                (fun uu____23563  ->
                                                   match uu____23563 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23600 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23600
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23621
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23621
                                                              then
                                                                let uu____23626
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23628
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23626
                                                                  uu____23628
                                                              else ());
                                                             (let uu____23634
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23634
                                                                (fun
                                                                   uu____23670
                                                                    ->
                                                                   match uu____23670
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
                    | uu____23799 -> FStar_Pervasives_Native.None  in
                  let uu____23840 = solve_branches wl brs1 brs2  in
                  (match uu____23840 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23866 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23866 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23893 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23893 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23927 =
                                FStar_List.map
                                  (fun uu____23939  ->
                                     match uu____23939 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23927  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23948 =
                              let uu____23949 =
                                let uu____23950 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23950
                                  (let uu___3375_23958 = wl3  in
                                   {
                                     attempting =
                                       (uu___3375_23958.attempting);
                                     wl_deferred =
                                       (uu___3375_23958.wl_deferred);
                                     ctr = (uu___3375_23958.ctr);
                                     defer_ok = (uu___3375_23958.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3375_23958.umax_heuristic_ok);
                                     tcenv = (uu___3375_23958.tcenv);
                                     wl_implicits =
                                       (uu___3375_23958.wl_implicits)
                                   })
                                 in
                              solve env uu____23949  in
                            (match uu____23948 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23963 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23972 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23972 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23975,uu____23976) ->
                  let head1 =
                    let uu____24000 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24000
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24046 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24046
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24092 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24092
                    then
                      let uu____24096 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24098 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24100 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24096 uu____24098 uu____24100
                    else ());
                   (let no_free_uvars t =
                      (let uu____24114 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24114) &&
                        (let uu____24118 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24118)
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
                      let uu____24137 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24137 = FStar_Syntax_Util.Equal  in
                    let uu____24138 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24138
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24142 = equal t1 t2  in
                         (if uu____24142
                          then
                            let uu____24145 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24145
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24150 =
                            let uu____24157 = equal t1 t2  in
                            if uu____24157
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24170 = mk_eq2 wl env orig t1 t2  in
                               match uu____24170 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24150 with
                          | (guard,wl1) ->
                              let uu____24191 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24191))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24194,uu____24195) ->
                  let head1 =
                    let uu____24203 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24203
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24249 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24249
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24295 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24295
                    then
                      let uu____24299 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24301 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24303 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24299 uu____24301 uu____24303
                    else ());
                   (let no_free_uvars t =
                      (let uu____24317 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24317) &&
                        (let uu____24321 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24321)
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
                      let uu____24340 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24340 = FStar_Syntax_Util.Equal  in
                    let uu____24341 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24341
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24345 = equal t1 t2  in
                         (if uu____24345
                          then
                            let uu____24348 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24348
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24353 =
                            let uu____24360 = equal t1 t2  in
                            if uu____24360
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24373 = mk_eq2 wl env orig t1 t2  in
                               match uu____24373 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24353 with
                          | (guard,wl1) ->
                              let uu____24394 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24394))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24397,uu____24398) ->
                  let head1 =
                    let uu____24400 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24400
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24446 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24446
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24492 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24492
                    then
                      let uu____24496 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24498 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24500 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24496 uu____24498 uu____24500
                    else ());
                   (let no_free_uvars t =
                      (let uu____24514 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24514) &&
                        (let uu____24518 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24518)
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
                      let uu____24537 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24537 = FStar_Syntax_Util.Equal  in
                    let uu____24538 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24538
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24542 = equal t1 t2  in
                         (if uu____24542
                          then
                            let uu____24545 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24545
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24550 =
                            let uu____24557 = equal t1 t2  in
                            if uu____24557
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24570 = mk_eq2 wl env orig t1 t2  in
                               match uu____24570 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24550 with
                          | (guard,wl1) ->
                              let uu____24591 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24591))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24594,uu____24595) ->
                  let head1 =
                    let uu____24597 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24597
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24643 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24643
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24689 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24689
                    then
                      let uu____24693 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24695 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24697 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24693 uu____24695 uu____24697
                    else ());
                   (let no_free_uvars t =
                      (let uu____24711 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24711) &&
                        (let uu____24715 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24715)
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
                      let uu____24734 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24734 = FStar_Syntax_Util.Equal  in
                    let uu____24735 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24735
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24739 = equal t1 t2  in
                         (if uu____24739
                          then
                            let uu____24742 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24742
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24747 =
                            let uu____24754 = equal t1 t2  in
                            if uu____24754
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24767 = mk_eq2 wl env orig t1 t2  in
                               match uu____24767 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24747 with
                          | (guard,wl1) ->
                              let uu____24788 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24788))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24791,uu____24792) ->
                  let head1 =
                    let uu____24794 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24794
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24840 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24840
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24886 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24886
                    then
                      let uu____24890 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24892 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24894 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24890 uu____24892 uu____24894
                    else ());
                   (let no_free_uvars t =
                      (let uu____24908 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24908) &&
                        (let uu____24912 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24912)
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
                      let uu____24931 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24931 = FStar_Syntax_Util.Equal  in
                    let uu____24932 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24932
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24936 = equal t1 t2  in
                         (if uu____24936
                          then
                            let uu____24939 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24939
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24944 =
                            let uu____24951 = equal t1 t2  in
                            if uu____24951
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24964 = mk_eq2 wl env orig t1 t2  in
                               match uu____24964 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24944 with
                          | (guard,wl1) ->
                              let uu____24985 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24985))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24988,uu____24989) ->
                  let head1 =
                    let uu____25007 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25007
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25053 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25053
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25099 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25099
                    then
                      let uu____25103 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25105 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25107 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25103 uu____25105 uu____25107
                    else ());
                   (let no_free_uvars t =
                      (let uu____25121 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25121) &&
                        (let uu____25125 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25125)
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
                      let uu____25144 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25144 = FStar_Syntax_Util.Equal  in
                    let uu____25145 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25145
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25149 = equal t1 t2  in
                         (if uu____25149
                          then
                            let uu____25152 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25152
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25157 =
                            let uu____25164 = equal t1 t2  in
                            if uu____25164
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25177 = mk_eq2 wl env orig t1 t2  in
                               match uu____25177 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25157 with
                          | (guard,wl1) ->
                              let uu____25198 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25198))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25201,FStar_Syntax_Syntax.Tm_match uu____25202) ->
                  let head1 =
                    let uu____25226 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25226
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25272 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25272
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25318 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25318
                    then
                      let uu____25322 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25324 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25326 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25322 uu____25324 uu____25326
                    else ());
                   (let no_free_uvars t =
                      (let uu____25340 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25340) &&
                        (let uu____25344 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25344)
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
                      let uu____25363 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25363 = FStar_Syntax_Util.Equal  in
                    let uu____25364 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25364
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25368 = equal t1 t2  in
                         (if uu____25368
                          then
                            let uu____25371 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25371
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25376 =
                            let uu____25383 = equal t1 t2  in
                            if uu____25383
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25396 = mk_eq2 wl env orig t1 t2  in
                               match uu____25396 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25376 with
                          | (guard,wl1) ->
                              let uu____25417 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25417))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25420,FStar_Syntax_Syntax.Tm_uinst uu____25421) ->
                  let head1 =
                    let uu____25429 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25429
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25475 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25475
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25521 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25521
                    then
                      let uu____25525 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25527 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25529 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25525 uu____25527 uu____25529
                    else ());
                   (let no_free_uvars t =
                      (let uu____25543 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25543) &&
                        (let uu____25547 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25547)
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
                      let uu____25566 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25566 = FStar_Syntax_Util.Equal  in
                    let uu____25567 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25567
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25571 = equal t1 t2  in
                         (if uu____25571
                          then
                            let uu____25574 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25574
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25579 =
                            let uu____25586 = equal t1 t2  in
                            if uu____25586
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25599 = mk_eq2 wl env orig t1 t2  in
                               match uu____25599 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25579 with
                          | (guard,wl1) ->
                              let uu____25620 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25620))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25623,FStar_Syntax_Syntax.Tm_name uu____25624) ->
                  let head1 =
                    let uu____25626 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25626
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25672 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25672
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25712 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25712
                    then
                      let uu____25716 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25718 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25720 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25716 uu____25718 uu____25720
                    else ());
                   (let no_free_uvars t =
                      (let uu____25734 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25734) &&
                        (let uu____25738 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25738)
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
                      let uu____25757 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25757 = FStar_Syntax_Util.Equal  in
                    let uu____25758 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25758
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25762 = equal t1 t2  in
                         (if uu____25762
                          then
                            let uu____25765 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25765
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25770 =
                            let uu____25777 = equal t1 t2  in
                            if uu____25777
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25790 = mk_eq2 wl env orig t1 t2  in
                               match uu____25790 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25770 with
                          | (guard,wl1) ->
                              let uu____25811 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25811))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25814,FStar_Syntax_Syntax.Tm_constant uu____25815) ->
                  let head1 =
                    let uu____25817 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25817
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25857 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25857
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25897 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25897
                    then
                      let uu____25901 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25903 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25905 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25901 uu____25903 uu____25905
                    else ());
                   (let no_free_uvars t =
                      (let uu____25919 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25919) &&
                        (let uu____25923 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25923)
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
                      let uu____25942 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25942 = FStar_Syntax_Util.Equal  in
                    let uu____25943 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25943
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25947 = equal t1 t2  in
                         (if uu____25947
                          then
                            let uu____25950 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25950
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25955 =
                            let uu____25962 = equal t1 t2  in
                            if uu____25962
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25975 = mk_eq2 wl env orig t1 t2  in
                               match uu____25975 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25955 with
                          | (guard,wl1) ->
                              let uu____25996 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25996))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25999,FStar_Syntax_Syntax.Tm_fvar uu____26000) ->
                  let head1 =
                    let uu____26002 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26002
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26048 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26048
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26094 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26094
                    then
                      let uu____26098 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26100 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26102 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26098 uu____26100 uu____26102
                    else ());
                   (let no_free_uvars t =
                      (let uu____26116 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26116) &&
                        (let uu____26120 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26120)
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
                      let uu____26139 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26139 = FStar_Syntax_Util.Equal  in
                    let uu____26140 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26140
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26144 = equal t1 t2  in
                         (if uu____26144
                          then
                            let uu____26147 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26147
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26152 =
                            let uu____26159 = equal t1 t2  in
                            if uu____26159
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26172 = mk_eq2 wl env orig t1 t2  in
                               match uu____26172 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26152 with
                          | (guard,wl1) ->
                              let uu____26193 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26193))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26196,FStar_Syntax_Syntax.Tm_app uu____26197) ->
                  let head1 =
                    let uu____26215 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26215
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26255 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26255
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26295 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26295
                    then
                      let uu____26299 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26301 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26303 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26299 uu____26301 uu____26303
                    else ());
                   (let no_free_uvars t =
                      (let uu____26317 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26317) &&
                        (let uu____26321 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26321)
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
                      let uu____26340 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26340 = FStar_Syntax_Util.Equal  in
                    let uu____26341 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26341
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26345 = equal t1 t2  in
                         (if uu____26345
                          then
                            let uu____26348 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26348
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26353 =
                            let uu____26360 = equal t1 t2  in
                            if uu____26360
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26373 = mk_eq2 wl env orig t1 t2  in
                               match uu____26373 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26353 with
                          | (guard,wl1) ->
                              let uu____26394 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26394))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26397,FStar_Syntax_Syntax.Tm_let uu____26398) ->
                  let uu____26425 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26425
                  then
                    let uu____26428 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26428
                  else
                    (let uu____26431 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26431 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26434,uu____26435) ->
                  let uu____26449 =
                    let uu____26455 =
                      let uu____26457 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26459 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26461 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26463 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26457 uu____26459 uu____26461 uu____26463
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26455)
                     in
                  FStar_Errors.raise_error uu____26449
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26467,FStar_Syntax_Syntax.Tm_let uu____26468) ->
                  let uu____26482 =
                    let uu____26488 =
                      let uu____26490 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26492 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26494 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26496 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26490 uu____26492 uu____26494 uu____26496
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26488)
                     in
                  FStar_Errors.raise_error uu____26482
                    t1.FStar_Syntax_Syntax.pos
              | uu____26500 ->
                  let uu____26505 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26505 orig))))

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
          (let uu____26571 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26571
           then
             let uu____26576 =
               let uu____26578 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26578  in
             let uu____26579 =
               let uu____26581 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26581  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26576 uu____26579
           else ());
          (let uu____26585 =
             let uu____26587 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26587  in
           if uu____26585
           then
             let uu____26590 =
               mklstr
                 (fun uu____26597  ->
                    let uu____26598 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26600 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26598 uu____26600)
                in
             giveup env uu____26590 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26622 =
                  mklstr
                    (fun uu____26629  ->
                       let uu____26630 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26632 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26630 uu____26632)
                   in
                giveup env uu____26622 orig)
             else
               (let uu____26637 =
                  FStar_List.fold_left2
                    (fun uu____26658  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26658 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26679 =
                                 let uu____26684 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26685 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26684
                                   FStar_TypeChecker_Common.EQ uu____26685
                                   "effect universes"
                                  in
                               (match uu____26679 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26637 with
                | (univ_sub_probs,wl1) ->
                    let uu____26705 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26705 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26713 =
                           FStar_List.fold_right2
                             (fun uu____26750  ->
                                fun uu____26751  ->
                                  fun uu____26752  ->
                                    match (uu____26750, uu____26751,
                                            uu____26752)
                                    with
                                    | ((a1,uu____26796),(a2,uu____26798),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26831 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26831 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26713 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26858 =
                                  let uu____26861 =
                                    let uu____26864 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26864
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26861
                                   in
                                FStar_List.append univ_sub_probs uu____26858
                                 in
                              let guard =
                                let guard =
                                  let uu____26886 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26886  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3527_26895 = wl3  in
                                {
                                  attempting = (uu___3527_26895.attempting);
                                  wl_deferred = (uu___3527_26895.wl_deferred);
                                  ctr = (uu___3527_26895.ctr);
                                  defer_ok = (uu___3527_26895.defer_ok);
                                  smt_ok = (uu___3527_26895.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3527_26895.umax_heuristic_ok);
                                  tcenv = (uu___3527_26895.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26897 = attempt sub_probs wl5  in
                              solve env uu____26897))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26915 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26915
           then
             let uu____26920 =
               let uu____26922 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26922
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26924 =
               let uu____26926 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26926
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26920 uu____26924
           else ());
          (let uu____26931 =
             let uu____26936 =
               let uu____26941 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26941
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26936
               (fun uu____26958  ->
                  match uu____26958 with
                  | (c,g) ->
                      let uu____26969 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26969, g))
              in
           match uu____26931 with
           | (c12,g_lift) ->
               ((let uu____26973 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26973
                 then
                   let uu____26978 =
                     let uu____26980 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26980
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26982 =
                     let uu____26984 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26984
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26978 uu____26982
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3547_26994 = wl  in
                     {
                       attempting = (uu___3547_26994.attempting);
                       wl_deferred = (uu___3547_26994.wl_deferred);
                       ctr = (uu___3547_26994.ctr);
                       defer_ok = (uu___3547_26994.defer_ok);
                       smt_ok = (uu___3547_26994.smt_ok);
                       umax_heuristic_ok =
                         (uu___3547_26994.umax_heuristic_ok);
                       tcenv = (uu___3547_26994.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26995 =
                     let rec is_uvar t =
                       let uu____27009 =
                         let uu____27010 = FStar_Syntax_Subst.compress t  in
                         uu____27010.FStar_Syntax_Syntax.n  in
                       match uu____27009 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27014 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27029) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27035) ->
                           is_uvar t1
                       | uu____27060 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27094  ->
                          fun uu____27095  ->
                            fun uu____27096  ->
                              match (uu____27094, uu____27095, uu____27096)
                              with
                              | ((a1,uu____27140),(a2,uu____27142),(is_sub_probs,wl2))
                                  ->
                                  let uu____27175 = is_uvar a1  in
                                  if uu____27175
                                  then
                                    ((let uu____27185 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27185
                                      then
                                        let uu____27190 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27192 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27190 uu____27192
                                      else ());
                                     (let uu____27197 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27197 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26995 with
                   | (is_sub_probs,wl2) ->
                       let uu____27225 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27225 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27233 =
                              let uu____27238 =
                                let uu____27239 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27239
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27238
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27233 with
                             | (uu____27246,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27257 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27259 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27257 s uu____27259
                                    in
                                 let uu____27262 =
                                   let uu____27291 =
                                     let uu____27292 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27292.FStar_Syntax_Syntax.n  in
                                   match uu____27291 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27352 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27352 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27415 =
                                              let uu____27434 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27434
                                                (fun uu____27538  ->
                                                   match uu____27538 with
                                                   | (l1,l2) ->
                                                       let uu____27611 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27611))
                                               in
                                            (match uu____27415 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27716 ->
                                       let uu____27717 =
                                         let uu____27723 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27723)
                                          in
                                       FStar_Errors.raise_error uu____27717 r
                                    in
                                 (match uu____27262 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27799 =
                                        let uu____27806 =
                                          let uu____27807 =
                                            let uu____27808 =
                                              let uu____27815 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27815,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27808
                                             in
                                          [uu____27807]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27806
                                          (fun b  ->
                                             let uu____27831 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27833 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27835 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27831 uu____27833
                                               uu____27835) r
                                         in
                                      (match uu____27799 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27845 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27845
                                             then
                                               let uu____27850 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27859 =
                                                          let uu____27861 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27861
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27859) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27850
                                             else ());
                                            (let wl4 =
                                               let uu___3619_27869 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3619_27869.attempting);
                                                 wl_deferred =
                                                   (uu___3619_27869.wl_deferred);
                                                 ctr = (uu___3619_27869.ctr);
                                                 defer_ok =
                                                   (uu___3619_27869.defer_ok);
                                                 smt_ok =
                                                   (uu___3619_27869.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3619_27869.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3619_27869.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27894 =
                                                        let uu____27901 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27901, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27894) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27918 =
                                               let f_sort_is =
                                                 let uu____27928 =
                                                   let uu____27929 =
                                                     let uu____27932 =
                                                       let uu____27933 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27933.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27932
                                                      in
                                                   uu____27929.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27928 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27944,uu____27945::is)
                                                     ->
                                                     let uu____27987 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27987
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28020 ->
                                                     let uu____28021 =
                                                       let uu____28027 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28027)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28021 r
                                                  in
                                               let uu____28033 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28068  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28068
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28089 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28089
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28033
                                                in
                                             match uu____27918 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28114 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28114
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28115 =
                                                   let g_sort_is =
                                                     let uu____28125 =
                                                       let uu____28126 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28126.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28125 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28131,uu____28132::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28192 ->
                                                         let uu____28193 =
                                                           let uu____28199 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28199)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28193 r
                                                      in
                                                   let uu____28205 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28240  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28240
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28261
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28261
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28205
                                                    in
                                                 (match uu____28115 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28288 =
                                                          let uu____28293 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28294 =
                                                            let uu____28295 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28295
                                                             in
                                                          (uu____28293,
                                                            uu____28294)
                                                           in
                                                        match uu____28288
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28323 =
                                                          let uu____28326 =
                                                            let uu____28329 =
                                                              let uu____28332
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28332
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28329
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28326
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28323
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28356 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28356
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
                                                        let uu____28367 =
                                                          let uu____28370 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28373 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28373)
                                                            uu____28370
                                                           in
                                                        solve_prob orig
                                                          uu____28367 [] wl6
                                                         in
                                                      let uu____28374 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28374))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28397 =
            let univs =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28399 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28399]
              | x -> x  in
            let c12 =
              let uu___3685_28402 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3685_28402.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3685_28402.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3685_28402.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3685_28402.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28403 =
              let uu____28408 =
                FStar_All.pipe_right
                  (let uu___3688_28410 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3688_28410.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3688_28410.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3688_28410.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3688_28410.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28408
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28403
              (fun uu____28424  ->
                 match uu____28424 with
                 | (c,g) ->
                     let uu____28431 =
                       let uu____28433 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28433  in
                     if uu____28431
                     then
                       let uu____28436 =
                         let uu____28442 =
                           let uu____28444 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28446 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28444 uu____28446
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28442)
                          in
                       FStar_Errors.raise_error uu____28436 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28452 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28452
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28458 = lift_c1 ()  in
               solve_eq uu____28458 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___28_28467  ->
                         match uu___28_28467 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28472 -> false))
                  in
               let uu____28474 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28504)::uu____28505,(wp2,uu____28507)::uu____28508)
                     -> (wp1, wp2)
                 | uu____28581 ->
                     let uu____28606 =
                       let uu____28612 =
                         let uu____28614 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28616 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28614 uu____28616
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28612)
                        in
                     FStar_Errors.raise_error uu____28606
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28474 with
               | (wpc1,wpc2) ->
                   let uu____28626 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28626
                   then
                     let uu____28629 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28629 wl
                   else
                     (let uu____28633 =
                        let uu____28640 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28640  in
                      match uu____28633 with
                      | (c2_decl,qualifiers) ->
                          let uu____28661 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28661
                          then
                            let c1_repr =
                              let uu____28668 =
                                let uu____28669 =
                                  let uu____28670 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28670  in
                                let uu____28671 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28669 uu____28671
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28668
                               in
                            let c2_repr =
                              let uu____28674 =
                                let uu____28675 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28676 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28675 uu____28676
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28674
                               in
                            let uu____28678 =
                              let uu____28683 =
                                let uu____28685 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28687 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28685
                                  uu____28687
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28683
                               in
                            (match uu____28678 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28693 = attempt [prob] wl2  in
                                 solve env uu____28693)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28713 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28713
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28736 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28736
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
                                        let uu____28746 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28746 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28753 =
                                        let uu____28760 =
                                          let uu____28761 =
                                            let uu____28778 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28781 =
                                              let uu____28792 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28792; wpc1_2]  in
                                            (uu____28778, uu____28781)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28761
                                           in
                                        FStar_Syntax_Syntax.mk uu____28760
                                         in
                                      uu____28753
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
                                     let uu____28841 =
                                       let uu____28848 =
                                         let uu____28849 =
                                           let uu____28866 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28869 =
                                             let uu____28880 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28889 =
                                               let uu____28900 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28900; wpc1_2]  in
                                             uu____28880 :: uu____28889  in
                                           (uu____28866, uu____28869)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28849
                                          in
                                       FStar_Syntax_Syntax.mk uu____28848  in
                                     uu____28841 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28954 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28954
                              then
                                let uu____28959 =
                                  let uu____28961 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28961
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28959
                              else ());
                             (let uu____28965 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28965 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28974 =
                                      let uu____28977 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____28980  ->
                                           FStar_Pervasives_Native.Some
                                             uu____28980) uu____28977
                                       in
                                    solve_prob orig uu____28974 [] wl1  in
                                  let uu____28981 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28981))))
           in
        let uu____28982 = FStar_Util.physical_equality c1 c2  in
        if uu____28982
        then
          let uu____28985 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28985
        else
          ((let uu____28989 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28989
            then
              let uu____28994 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28996 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28994
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28996
            else ());
           (let uu____29001 =
              let uu____29010 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29013 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29010, uu____29013)  in
            match uu____29001 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29031),FStar_Syntax_Syntax.Total
                    (t2,uu____29033)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29050 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29050 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29052,FStar_Syntax_Syntax.Total uu____29053) ->
                     let uu____29070 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29070 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29074),FStar_Syntax_Syntax.Total
                    (t2,uu____29076)) ->
                     let uu____29093 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29093 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29096),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29098)) ->
                     let uu____29115 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29115 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29118),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29120)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29137 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29137 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29140),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29142)) ->
                     let uu____29159 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29159 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29162,FStar_Syntax_Syntax.Comp uu____29163) ->
                     let uu____29172 =
                       let uu___3812_29175 = problem  in
                       let uu____29178 =
                         let uu____29179 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29179
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3812_29175.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29178;
                         FStar_TypeChecker_Common.relation =
                           (uu___3812_29175.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3812_29175.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3812_29175.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3812_29175.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3812_29175.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3812_29175.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3812_29175.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3812_29175.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29172 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29180,FStar_Syntax_Syntax.Comp uu____29181) ->
                     let uu____29190 =
                       let uu___3812_29193 = problem  in
                       let uu____29196 =
                         let uu____29197 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29197
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3812_29193.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29196;
                         FStar_TypeChecker_Common.relation =
                           (uu___3812_29193.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3812_29193.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3812_29193.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3812_29193.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3812_29193.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3812_29193.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3812_29193.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3812_29193.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29190 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29198,FStar_Syntax_Syntax.GTotal uu____29199) ->
                     let uu____29208 =
                       let uu___3824_29211 = problem  in
                       let uu____29214 =
                         let uu____29215 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29215
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3824_29211.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3824_29211.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3824_29211.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29214;
                         FStar_TypeChecker_Common.element =
                           (uu___3824_29211.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3824_29211.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3824_29211.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3824_29211.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3824_29211.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3824_29211.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29208 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29216,FStar_Syntax_Syntax.Total uu____29217) ->
                     let uu____29226 =
                       let uu___3824_29229 = problem  in
                       let uu____29232 =
                         let uu____29233 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29233
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3824_29229.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3824_29229.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3824_29229.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29232;
                         FStar_TypeChecker_Common.element =
                           (uu___3824_29229.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3824_29229.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3824_29229.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3824_29229.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3824_29229.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3824_29229.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29226 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29234,FStar_Syntax_Syntax.Comp uu____29235) ->
                     let uu____29236 =
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
                     if uu____29236
                     then
                       let uu____29239 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29239 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29246 =
                            let uu____29251 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29251
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29260 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29261 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29260, uu____29261))
                             in
                          match uu____29246 with
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
                           (let uu____29269 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29269
                            then
                              let uu____29274 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29276 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29274 uu____29276
                            else ());
                           (let uu____29281 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29281 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29284 =
                                  mklstr
                                    (fun uu____29291  ->
                                       let uu____29292 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29294 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29292 uu____29294)
                                   in
                                giveup env uu____29284 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29305 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29305 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29355 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29355 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29380 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29411  ->
                match uu____29411 with
                | (u1,u2) ->
                    let uu____29419 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29421 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29419 uu____29421))
         in
      FStar_All.pipe_right uu____29380 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29458,[])) when
          let uu____29485 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29485 -> "{}"
      | uu____29488 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29515 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29515
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29527 =
              FStar_List.map
                (fun uu____29540  ->
                   match uu____29540 with
                   | (uu____29547,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29527 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29558 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29558 imps
  
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
                  let uu____29615 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29615
                  then
                    let uu____29623 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29625 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29623
                      (rel_to_string rel) uu____29625
                  else "TOP"  in
                let uu____29631 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29631 with
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
              let uu____29691 =
                let uu____29694 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____29697  ->
                     FStar_Pervasives_Native.Some uu____29697) uu____29694
                 in
              FStar_Syntax_Syntax.new_bv uu____29691 t1  in
            let uu____29698 =
              let uu____29703 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29703
               in
            match uu____29698 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29761 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29761
         then
           let uu____29766 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29766
         else ());
        (let uu____29773 =
           FStar_Util.record_time (fun uu____29780  -> solve env probs)  in
         match uu____29773 with
         | (sol,ms) ->
             ((let uu____29792 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29792
               then
                 let uu____29797 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29797
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29810 =
                     FStar_Util.record_time
                       (fun uu____29817  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29810 with
                    | ((),ms1) ->
                        ((let uu____29828 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29828
                          then
                            let uu____29833 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29833
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29845 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29845
                     then
                       let uu____29852 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29852
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
          ((let uu____29878 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29878
            then
              let uu____29883 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29883
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29891 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29891
             then
               let uu____29896 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29896
             else ());
            (let f2 =
               let uu____29902 =
                 let uu____29903 = FStar_Syntax_Util.unmeta f1  in
                 uu____29903.FStar_Syntax_Syntax.n  in
               match uu____29902 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29907 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3941_29908 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3941_29908.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3941_29908.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3941_29908.FStar_TypeChecker_Common.implicits)
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
            let uu____29951 =
              let uu____29952 =
                let uu____29953 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____29954  ->
                       FStar_TypeChecker_Common.NonTrivial uu____29954)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29953;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29952  in
            FStar_All.pipe_left
              (fun uu____29961  -> FStar_Pervasives_Native.Some uu____29961)
              uu____29951
  
let with_guard_no_simp :
  'uuuuuu29971 .
    'uuuuuu29971 ->
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
            let uu____30011 =
              let uu____30012 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30013  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30013)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30012;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30011
  
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
          (let uu____30046 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30046
           then
             let uu____30051 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30053 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30051
               uu____30053
           else ());
          (let uu____30058 =
             let uu____30063 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30063
              in
           match uu____30058 with
           | (prob,wl) ->
               let g =
                 let uu____30071 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30079  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30071  in
               ((let uu____30097 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30097
                 then
                   let uu____30102 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30102
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
        let uu____30123 = try_teq true env t1 t2  in
        match uu____30123 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30128 = FStar_TypeChecker_Env.get_range env  in
              let uu____30129 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30128 uu____30129);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30137 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30137
              then
                let uu____30142 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30144 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30146 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30142
                  uu____30144 uu____30146
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
        (let uu____30170 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30170
         then
           let uu____30175 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30177 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30175
             uu____30177
         else ());
        (let uu____30182 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30182 with
         | (prob,x,wl) ->
             let g =
               let uu____30197 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30206  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30197  in
             ((let uu____30224 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30224
               then
                 let uu____30229 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30229
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30237 =
                     let uu____30238 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30238 g1  in
                   FStar_Pervasives_Native.Some uu____30237)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30260 = FStar_TypeChecker_Env.get_range env  in
          let uu____30261 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30260 uu____30261
  
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
        (let uu____30290 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30290
         then
           let uu____30295 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30297 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30295 uu____30297
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30308 =
           let uu____30315 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30315 "sub_comp"
            in
         match uu____30308 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30328 =
                 FStar_Util.record_time
                   (fun uu____30340  ->
                      let uu____30341 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30350  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30341)
                  in
               match uu____30328 with
               | (r,ms) ->
                   ((let uu____30378 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30378
                     then
                       let uu____30383 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30385 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30387 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30383 uu____30385
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30387
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
      fun uu____30425  ->
        match uu____30425 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30468 =
                 let uu____30474 =
                   let uu____30476 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30478 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30476 uu____30478
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30474)  in
               let uu____30482 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30468 uu____30482)
               in
            let equiv v v' =
              let uu____30495 =
                let uu____30500 = FStar_Syntax_Subst.compress_univ v  in
                let uu____30501 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30500, uu____30501)  in
              match uu____30495 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30525 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____30556 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____30556 with
                      | FStar_Syntax_Syntax.U_unif uu____30563 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30594  ->
                                    match uu____30594 with
                                    | (u,v') ->
                                        let uu____30603 = equiv v v'  in
                                        if uu____30603
                                        then
                                          let uu____30608 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____30608 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____30629 -> []))
               in
            let uu____30634 =
              let wl =
                let uu___4052_30638 = empty_worklist env  in
                {
                  attempting = (uu___4052_30638.attempting);
                  wl_deferred = (uu___4052_30638.wl_deferred);
                  ctr = (uu___4052_30638.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4052_30638.smt_ok);
                  umax_heuristic_ok = (uu___4052_30638.umax_heuristic_ok);
                  tcenv = (uu___4052_30638.tcenv);
                  wl_implicits = (uu___4052_30638.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30657  ->
                      match uu____30657 with
                      | (lb,v) ->
                          let uu____30664 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____30664 with
                           | USolved wl1 -> ()
                           | uu____30667 -> fail lb v)))
               in
            let rec check_ineq uu____30678 =
              match uu____30678 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30690) -> true
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
                      uu____30718,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30720,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30733) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____30741,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____30750 -> false)
               in
            let uu____30756 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30773  ->
                      match uu____30773 with
                      | (u,v) ->
                          let uu____30781 = check_ineq (u, v)  in
                          if uu____30781
                          then true
                          else
                            ((let uu____30789 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30789
                              then
                                let uu____30794 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30796 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____30794
                                  uu____30796
                              else ());
                             false)))
               in
            if uu____30756
            then ()
            else
              ((let uu____30806 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30806
                then
                  ((let uu____30812 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30812);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30824 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30824))
                else ());
               (let uu____30837 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30837))
  
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
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun smt_ok  ->
      fun env  ->
        fun g  ->
          let fail uu____30917 =
            match uu____30917 with
            | (d,s) ->
                let msg = explain env d s  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d)
             in
          let wl =
            let uu___4130_30940 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
            {
              attempting = (uu___4130_30940.attempting);
              wl_deferred = (uu___4130_30940.wl_deferred);
              ctr = (uu___4130_30940.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4130_30940.umax_heuristic_ok);
              tcenv = (uu___4130_30940.tcenv);
              wl_implicits = (uu___4130_30940.wl_implicits)
            }  in
          (let uu____30943 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30943
           then
             let uu____30948 = FStar_Util.string_of_bool defer_ok  in
             let uu____30950 = wl_to_string wl  in
             let uu____30952 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits)
                in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____30948 uu____30950 uu____30952
           else ());
          (let g1 =
             let uu____30958 = solve_and_commit env wl fail  in
             match uu____30958 with
             | FStar_Pervasives_Native.Some
                 (uu____30965::uu____30966,uu____30967) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred,imps) ->
                 let uu___4145_30996 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4145_30996.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4145_30996.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____30997 ->
                 failwith "Impossible: should have raised a failure already"
              in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let uu___4150_31006 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4150_31006.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred =
                (uu___4150_31006.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs = ([], []);
              FStar_TypeChecker_Common.implicits =
                (uu___4150_31006.FStar_TypeChecker_Common.implicits)
            }))
  
let (solve_deferred_constraints' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun smt_ok  ->
    fun env  -> fun g  -> try_solve_deferred_constraints false smt_ok env g
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> solve_deferred_constraints' true env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true true env g 
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
          let debug =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints' use_smt env g  in
          let ret_g =
            let uu___4165_31103 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4165_31103.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4165_31103.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4165_31103.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31104 =
            let uu____31106 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31106  in
          if uu____31104
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug
                  then
                    (let uu____31118 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31119 =
                       let uu____31121 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31121
                        in
                     FStar_Errors.diag uu____31118 uu____31119)
                  else ();
                  (let vc1 =
                     let uu____31127 =
                       let uu____31131 =
                         let uu____31133 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31133  in
                       FStar_Pervasives_Native.Some uu____31131  in
                     FStar_Profiling.profile
                       (fun uu____31136  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31127 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug
                   then
                     (let uu____31140 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31141 =
                        let uu____31143 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31143
                         in
                      FStar_Errors.diag uu____31140 uu____31141)
                   else ();
                   (let uu____31149 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31149
                      "discharge_guard'" env vc1);
                   (let uu____31151 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31151 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug
                           then
                             (let uu____31160 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31161 =
                                let uu____31163 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31163
                                 in
                              FStar_Errors.diag uu____31160 uu____31161)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug
                           then
                             (let uu____31173 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31174 =
                                let uu____31176 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31176
                                 in
                              FStar_Errors.diag uu____31173 uu____31174)
                           else ();
                           (let vcs =
                              let uu____31190 = FStar_Options.use_tactics ()
                                 in
                              if uu____31190
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31212  ->
                                     (let uu____31214 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____31216  -> ()) uu____31214);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31259  ->
                                              match uu____31259 with
                                              | (env1,goal,opts) ->
                                                  let uu____31275 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31275, opts)))))
                              else
                                (let uu____31279 =
                                   let uu____31286 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31286)  in
                                 [uu____31279])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31319  ->
                                    match uu____31319 with
                                    | (env1,goal,opts) ->
                                        let uu____31329 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31329 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal1 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              if debug
                                              then
                                                (let uu____31340 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31341 =
                                                   let uu____31343 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31345 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31343 uu____31345
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31340 uu____31341)
                                              else ();
                                              if debug
                                              then
                                                (let uu____31352 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31353 =
                                                   let uu____31355 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31355
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31352 uu____31353)
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
      let uu____31373 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31373 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31382 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31382
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31396 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31396 with
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
        let uu____31426 = try_teq false env t1 t2  in
        match uu____31426 with
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
            let uu____31470 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31470 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31483 ->
                     let uu____31496 =
                       let uu____31497 = FStar_Syntax_Subst.compress r  in
                       uu____31497.FStar_Syntax_Syntax.n  in
                     (match uu____31496 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31502) ->
                          unresolved ctx_u'
                      | uu____31519 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31543 = acc  in
            match uu____31543 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____31562 = hd  in
                     (match uu____31562 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____31573 = unresolved ctx_u  in
                             if uu____31573
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd :: out), changed) tl
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31597 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31597
                                     then
                                       let uu____31601 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31601
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31610 = teq_nosmt env1 t tm
                                          in
                                       match uu____31610 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4278_31620 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4278_31620.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4278_31620.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4278_31620.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4278_31620.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4278_31620.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4278_31620.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4278_31620.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4281_31628 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4281_31628.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4281_31628.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4281_31628.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl)))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl
                               else
                                 (let env1 =
                                    let uu___4285_31639 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4285_31639.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4285_31639.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4285_31639.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4285_31639.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4285_31639.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4285_31639.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4285_31639.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4285_31639.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4285_31639.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4285_31639.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4285_31639.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4285_31639.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4285_31639.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4285_31639.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4285_31639.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4285_31639.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4285_31639.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4285_31639.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4285_31639.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4285_31639.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4285_31639.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4285_31639.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4285_31639.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4285_31639.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4285_31639.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4285_31639.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4285_31639.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4285_31639.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4285_31639.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4285_31639.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4285_31639.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4285_31639.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4285_31639.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4285_31639.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4285_31639.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4285_31639.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4285_31639.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4285_31639.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4285_31639.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4285_31639.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4285_31639.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4285_31639.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4285_31639.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4285_31639.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4285_31639.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4290_31644 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4290_31644.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4290_31644.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4290_31644.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4290_31644.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4290_31644.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4290_31644.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4290_31644.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4290_31644.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4290_31644.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4290_31644.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4290_31644.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4290_31644.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4290_31644.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4290_31644.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4290_31644.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4290_31644.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4290_31644.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4290_31644.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4290_31644.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4290_31644.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4290_31644.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4290_31644.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4290_31644.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4290_31644.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4290_31644.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4290_31644.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4290_31644.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4290_31644.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4290_31644.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4290_31644.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4290_31644.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4290_31644.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4290_31644.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4290_31644.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4290_31644.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4290_31644.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4290_31644.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31649 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31649
                                   then
                                     let uu____31654 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31656 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31658 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31660 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31654 uu____31656 uu____31658
                                       reason uu____31660
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4296_31667  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31674 =
                                             let uu____31684 =
                                               let uu____31692 =
                                                 let uu____31694 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31696 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31698 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31694 uu____31696
                                                   uu____31698
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31692, r)
                                                in
                                             [uu____31684]  in
                                           FStar_Errors.add_errors
                                             uu____31674);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31717 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31728  ->
                                               let uu____31729 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31731 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31733 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31729 uu____31731
                                                 reason uu____31733)) env2 g1
                                         true
                                        in
                                     match uu____31717 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl)))))
             in
          let uu___4308_31741 = g  in
          let uu____31742 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4308_31741.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4308_31741.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4308_31741.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31742
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
        let uu____31782 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31782 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31783 = discharge_guard env g1  in
          FStar_All.pipe_left (fun uu____31784  -> ()) uu____31783
      | imp::uu____31786 ->
          let uu____31789 =
            let uu____31795 =
              let uu____31797 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31799 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31797 uu____31799
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31795)
             in
          FStar_Errors.raise_error uu____31789
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31819 = teq env t1 t2  in
        force_trivial_guard env uu____31819
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31838 = teq_nosmt env t1 t2  in
        match uu____31838 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4333_31857 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4333_31857.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4333_31857.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4333_31857.FStar_TypeChecker_Common.implicits)
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
        (let uu____31893 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31893
         then
           let uu____31898 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31900 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31898
             uu____31900
         else ());
        (let uu____31905 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31905 with
         | (prob,x,wl) ->
             let g =
               let uu____31924 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31933  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31924  in
             ((let uu____31951 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31951
               then
                 let uu____31956 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31958 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31960 =
                   let uu____31962 = FStar_Util.must g  in
                   guard_to_string env uu____31962  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31956 uu____31958 uu____31960
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
        let uu____31999 = check_subtyping env t1 t2  in
        match uu____31999 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32018 =
              let uu____32019 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32019 g  in
            FStar_Pervasives_Native.Some uu____32018
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32038 = check_subtyping env t1 t2  in
        match uu____32038 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32057 =
              let uu____32058 =
                let uu____32059 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32059]  in
              FStar_TypeChecker_Env.close_guard env uu____32058 g  in
            FStar_Pervasives_Native.Some uu____32057
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32097 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32097
         then
           let uu____32102 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32104 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32102
             uu____32104
         else ());
        (let uu____32109 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32109 with
         | (prob,x,wl) ->
             let g =
               let uu____32124 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32133  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32124  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32154 =
                      let uu____32155 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32155]  in
                    FStar_TypeChecker_Env.close_guard env uu____32154 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32196 = subtype_nosmt env t1 t2  in
        match uu____32196 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  