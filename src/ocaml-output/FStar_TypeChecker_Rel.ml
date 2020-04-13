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
                    let uu____570 = FStar_Syntax_Unionfind.fresh ()  in
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
                   (let uu____602 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____602
                    then
                      let uu____606 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____606
                    else ());
                   (ctx_uvar, t,
                     ((let uu___77_612 = wl  in
                       {
                         attempting = (uu___77_612.attempting);
                         wl_deferred = (uu___77_612.wl_deferred);
                         ctr = (uu___77_612.ctr);
                         defer_ok = (uu___77_612.defer_ok);
                         smt_ok = (uu___77_612.smt_ok);
                         umax_heuristic_ok = (uu___77_612.umax_heuristic_ok);
                         tcenv = (uu___77_612.tcenv);
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
            let uu___83_645 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___83_645.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___83_645.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___83_645.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___83_645.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___83_645.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___83_645.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___83_645.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___83_645.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___83_645.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___83_645.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___83_645.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___83_645.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___83_645.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___83_645.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___83_645.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___83_645.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___83_645.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___83_645.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___83_645.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___83_645.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___83_645.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___83_645.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___83_645.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___83_645.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___83_645.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___83_645.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___83_645.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___83_645.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___83_645.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___83_645.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___83_645.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___83_645.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___83_645.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___83_645.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___83_645.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___83_645.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___83_645.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___83_645.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___83_645.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___83_645.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___83_645.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___83_645.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___83_645.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___83_645.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___83_645.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____647 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____647 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____734 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____769 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____799 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____810 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____821 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_839  ->
    match uu___0_839 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____851 = FStar_Syntax_Util.head_and_args t  in
    match uu____851 with
    | (head,args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____914 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____916 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____931 =
                     let uu____933 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____933  in
                   FStar_Util.format1 "@<%s>" uu____931
                in
             let uu____937 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____914 uu____916 uu____937
         | uu____940 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_952  ->
      match uu___1_952 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____957 =
            let uu____961 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____963 =
              let uu____967 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____969 =
                let uu____973 =
                  let uu____977 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____977]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____973
                 in
              uu____967 :: uu____969  in
            uu____961 :: uu____963  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____957
      | FStar_TypeChecker_Common.CProb p ->
          let uu____988 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____990 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____992 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____988 uu____990
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____992
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1006  ->
      match uu___2_1006 with
      | UNIV (u,t) ->
          let x =
            let uu____1012 = FStar_Options.hide_uvar_nums ()  in
            if uu____1012
            then "?"
            else
              (let uu____1019 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1019 FStar_Util.string_of_int)
             in
          let uu____1023 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1023
      | TERM (u,t) ->
          let x =
            let uu____1030 = FStar_Options.hide_uvar_nums ()  in
            if uu____1030
            then "?"
            else
              (let uu____1037 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1037 FStar_Util.string_of_int)
             in
          let uu____1041 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s <- %s" x uu____1041
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  -> FStar_Common.string_of_list (uvi_to_string env) uvis
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1071 =
      let uu____1075 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1075
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1071 (FStar_String.concat ", ")
  
let args_to_string :
  'uuuuuu1094 .
    (FStar_Syntax_Syntax.term * 'uuuuuu1094) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1113 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1134  ->
              match uu____1134 with
              | (x,uu____1141) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1113 (FStar_String.concat " ")
  
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
        (let uu____1181 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1181
         then
           let uu____1186 = FStar_Thunk.force reason  in
           let uu____1189 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1186 uu____1189
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1212 = mklstr (fun uu____1215  -> reason)  in
        giveup env uu____1212 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1221  ->
    match uu___3_1221 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'uuuuuu1227 .
    'uuuuuu1227 FStar_TypeChecker_Common.problem ->
      'uuuuuu1227 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___147_1239 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___147_1239.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___147_1239.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___147_1239.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___147_1239.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___147_1239.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___147_1239.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___147_1239.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'uuuuuu1247 .
    'uuuuuu1247 FStar_TypeChecker_Common.problem ->
      'uuuuuu1247 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1267  ->
    match uu___4_1267 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1273  -> FStar_TypeChecker_Common.TProb uu____1273)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1279  -> FStar_TypeChecker_Common.CProb uu____1279)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1285  ->
    match uu___5_1285 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___159_1291 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___159_1291.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___159_1291.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___159_1291.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___159_1291.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___159_1291.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___159_1291.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___159_1291.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___159_1291.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___159_1291.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___163_1299 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___163_1299.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___163_1299.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___163_1299.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___163_1299.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___163_1299.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___163_1299.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___163_1299.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___163_1299.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___163_1299.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1312  ->
      match uu___6_1312 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1319  ->
    match uu___7_1319 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1332  ->
    match uu___8_1332 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1347  ->
    match uu___9_1347 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1362  ->
    match uu___10_1362 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1376  ->
    match uu___11_1376 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1390  ->
    match uu___12_1390 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1402  ->
    match uu___13_1402 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'uuuuuu1418 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu1418) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1448 =
          let uu____1450 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1450  in
        if uu____1448
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1487)::bs ->
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
          let uu____1534 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1558 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1558]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1534
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1586 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1610 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1610]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1586
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1657 =
          let uu____1659 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1659  in
        if uu____1657
        then ()
        else
          (let uu____1664 =
             let uu____1667 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1667
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1664 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1716 =
          let uu____1718 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1718  in
        if uu____1716
        then ()
        else
          (let uu____1723 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1723)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1743 =
        let uu____1745 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1745  in
      if uu____1743
      then ()
      else
        (let msgf m =
           let uu____1759 =
             let uu____1761 =
               let uu____1763 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1763 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1761  in
           Prims.op_Hat msg uu____1759  in
         (let uu____1768 = msgf "scope"  in
          let uu____1771 = p_scope prob  in
          def_scope_wf uu____1768 (p_loc prob) uu____1771);
         (let uu____1783 = msgf "guard"  in
          def_check_scoped uu____1783 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1790 = msgf "lhs"  in
                def_check_scoped uu____1790 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1793 = msgf "rhs"  in
                def_check_scoped uu____1793 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1800 = msgf "lhs"  in
                def_check_scoped_comp uu____1800 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1803 = msgf "rhs"  in
                def_check_scoped_comp uu____1803 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___256_1824 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___256_1824.wl_deferred);
          ctr = (uu___256_1824.ctr);
          defer_ok = (uu___256_1824.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___256_1824.umax_heuristic_ok);
          tcenv = (uu___256_1824.tcenv);
          wl_implicits = (uu___256_1824.wl_implicits)
        }
  
let wl_of_guard :
  'uuuuuu1832 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1832 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___260_1855 = empty_worklist env  in
      let uu____1856 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1856;
        wl_deferred = (uu___260_1855.wl_deferred);
        ctr = (uu___260_1855.ctr);
        defer_ok = (uu___260_1855.defer_ok);
        smt_ok = (uu___260_1855.smt_ok);
        umax_heuristic_ok = (uu___260_1855.umax_heuristic_ok);
        tcenv = (uu___260_1855.tcenv);
        wl_implicits = (uu___260_1855.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___265_1877 = wl  in
        {
          attempting = (uu___265_1877.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___265_1877.ctr);
          defer_ok = (uu___265_1877.defer_ok);
          smt_ok = (uu___265_1877.smt_ok);
          umax_heuristic_ok = (uu___265_1877.umax_heuristic_ok);
          tcenv = (uu___265_1877.tcenv);
          wl_implicits = (uu___265_1877.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1904 = FStar_Thunk.mkv reason  in defer uu____1904 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___273_1923 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___273_1923.wl_deferred);
         ctr = (uu___273_1923.ctr);
         defer_ok = (uu___273_1923.defer_ok);
         smt_ok = (uu___273_1923.smt_ok);
         umax_heuristic_ok = (uu___273_1923.umax_heuristic_ok);
         tcenv = (uu___273_1923.tcenv);
         wl_implicits = (uu___273_1923.wl_implicits)
       })
  
let mk_eq2 :
  'uuuuuu1937 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu1937 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1971 = FStar_Syntax_Util.type_u ()  in
            match uu____1971 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1983 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1983 with
                 | (uu____2001,tt,wl1) ->
                     let uu____2004 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2004, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2010  ->
    match uu___14_2010 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2016  -> FStar_TypeChecker_Common.TProb uu____2016)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2022  -> FStar_TypeChecker_Common.CProb uu____2022)
          (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2030 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2030 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2050  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'uuuuuu2092 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2092 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2092 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2092 FStar_TypeChecker_Common.problem * worklist)
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
                        let uu____2179 =
                          let uu____2188 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2188]  in
                        FStar_List.append scope uu____2179
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2231 =
                      let uu____2234 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2234  in
                    FStar_List.append uu____2231
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2253 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2253 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2279 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2279;
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
                  (let uu____2353 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2353 with
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
                  (let uu____2441 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2441 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'uuuuuu2479 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2479 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2479 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2479 FStar_TypeChecker_Common.problem * worklist)
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
                          let uu____2547 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2547]  in
                        let uu____2566 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2566
                     in
                  let uu____2569 =
                    let uu____2576 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___356_2587 = wl  in
                       {
                         attempting = (uu___356_2587.attempting);
                         wl_deferred = (uu___356_2587.wl_deferred);
                         ctr = (uu___356_2587.ctr);
                         defer_ok = (uu___356_2587.defer_ok);
                         smt_ok = (uu___356_2587.smt_ok);
                         umax_heuristic_ok =
                           (uu___356_2587.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___356_2587.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2576
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2569 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2605 =
                              let uu____2610 =
                                let uu____2611 =
                                  let uu____2620 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2620
                                   in
                                [uu____2611]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2610  in
                            uu____2605 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2648 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2648;
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
                let uu____2696 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2696;
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
  'uuuuuu2711 .
    worklist ->
      'uuuuuu2711 FStar_TypeChecker_Common.problem ->
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
              let uu____2744 =
                let uu____2747 =
                  let uu____2748 =
                    let uu____2755 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2755)  in
                  FStar_Syntax_Syntax.NT uu____2748  in
                [uu____2747]  in
              FStar_Syntax_Subst.subst uu____2744 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2777 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2777
        then
          let uu____2785 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2788 = prob_to_string env d  in
          let uu____2790 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2797 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2785 uu____2788 uu____2790 uu____2797
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2809 -> failwith "impossible"  in
           let uu____2812 =
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
           match uu____2812 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2855  ->
            match uu___15_2855 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2867 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2871 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2871 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2902  ->
           match uu___16_2902 with
           | UNIV uu____2905 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2912 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2912
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
        (fun uu___17_2940  ->
           match uu___17_2940 with
           | UNIV (u',t) ->
               let uu____2945 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2945
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2952 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2964 =
        let uu____2965 =
          let uu____2966 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2966
           in
        FStar_Syntax_Subst.compress uu____2965  in
      FStar_All.pipe_right uu____2964 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2978 =
        let uu____2979 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2979  in
      FStar_All.pipe_right uu____2978 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2991 =
        let uu____2995 =
          let uu____2997 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2997  in
        FStar_Pervasives_Native.Some uu____2995  in
      FStar_Profiling.profile (fun uu____3000  -> sn' env t) uu____2991
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
          let uu____3025 =
            let uu____3029 =
              let uu____3031 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3031  in
            FStar_Pervasives_Native.Some uu____3029  in
          FStar_Profiling.profile
            (fun uu____3034  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3025
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3042 = FStar_Syntax_Util.head_and_args t  in
    match uu____3042 with
    | (h,uu____3061) ->
        let uu____3086 =
          let uu____3087 = FStar_Syntax_Subst.compress h  in
          uu____3087.FStar_Syntax_Syntax.n  in
        (match uu____3086 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3092 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3105 =
        let uu____3109 =
          let uu____3111 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3111  in
        FStar_Pervasives_Native.Some uu____3109  in
      FStar_Profiling.profile
        (fun uu____3116  ->
           let uu____3117 = should_strongly_reduce t  in
           if uu____3117
           then
             let uu____3120 =
               let uu____3121 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3121  in
             FStar_All.pipe_right uu____3120 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3105 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'uuuuuu3132 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3132) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3132)
  =
  fun env  ->
    fun t  ->
      let uu____3155 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3155, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3207  ->
              match uu____3207 with
              | (x,imp) ->
                  let uu____3226 =
                    let uu___462_3227 = x  in
                    let uu____3228 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___462_3227.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___462_3227.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3228
                    }  in
                  (uu____3226, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3252 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3252
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3256 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3256
        | uu____3259 -> u2  in
      let uu____3260 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3260
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3277 =
          let uu____3281 =
            let uu____3283 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3283  in
          FStar_Pervasives_Native.Some uu____3281  in
        FStar_Profiling.profile
          (fun uu____3286  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3277 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3408 = norm_refinement env t12  in
                 match uu____3408 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3423;
                     FStar_Syntax_Syntax.vars = uu____3424;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3448 =
                       let uu____3450 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3452 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3450 uu____3452
                        in
                     failwith uu____3448)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3468 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm uu____3468
          | FStar_Syntax_Syntax.Tm_uinst uu____3469 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3506 =
                   let uu____3507 = FStar_Syntax_Subst.compress t1'  in
                   uu____3507.FStar_Syntax_Syntax.n  in
                 match uu____3506 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3522 -> aux true t1'
                 | uu____3530 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3545 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3576 =
                   let uu____3577 = FStar_Syntax_Subst.compress t1'  in
                   uu____3577.FStar_Syntax_Syntax.n  in
                 match uu____3576 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3592 -> aux true t1'
                 | uu____3600 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3615 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3662 =
                   let uu____3663 = FStar_Syntax_Subst.compress t1'  in
                   uu____3663.FStar_Syntax_Syntax.n  in
                 match uu____3662 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3678 -> aux true t1'
                 | uu____3686 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3701 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3716 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3731 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3746 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3761 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3790 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3823 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3844 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3871 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3899 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3936 ->
              let uu____3943 =
                let uu____3945 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3947 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3945 uu____3947
                 in
              failwith uu____3943
          | FStar_Syntax_Syntax.Tm_ascribed uu____3962 ->
              let uu____3989 =
                let uu____3991 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3993 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3991 uu____3993
                 in
              failwith uu____3989
          | FStar_Syntax_Syntax.Tm_delayed uu____4008 ->
              let uu____4023 =
                let uu____4025 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4027 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4025 uu____4027
                 in
              failwith uu____4023
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4042 =
                let uu____4044 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4046 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4044 uu____4046
                 in
              failwith uu____4042
           in
        let uu____4061 = whnf env t1  in aux false uu____4061
  
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
      let uu____4106 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4106 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4147 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4147, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta  ->
    fun env  ->
      fun t  ->
        let uu____4174 = base_and_refinement_maybe_delta delta env t  in
        match uu____4174 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4234  ->
    match uu____4234 with
    | (t_base,refopt) ->
        let uu____4265 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4265 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4307 =
      let uu____4311 =
        let uu____4314 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4339  ->
                  match uu____4339 with | (uu____4347,uu____4348,x) -> x))
           in
        FStar_List.append wl.attempting uu____4314  in
      FStar_List.map (wl_prob_to_string wl) uu____4311  in
    FStar_All.pipe_right uu____4307 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'uuuuuu4369 .
    ('uuuuuu4369 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4381  ->
    match uu____4381 with
    | (uu____4388,c,args) ->
        let uu____4391 = print_ctx_uvar c  in
        let uu____4393 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4391 uu____4393
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4403 = FStar_Syntax_Util.head_and_args t  in
    match uu____4403 with
    | (head,_args) ->
        let uu____4447 =
          let uu____4448 = FStar_Syntax_Subst.compress head  in
          uu____4448.FStar_Syntax_Syntax.n  in
        (match uu____4447 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4452 -> true
         | uu____4466 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4474 = FStar_Syntax_Util.head_and_args t  in
    match uu____4474 with
    | (head,_args) ->
        let uu____4517 =
          let uu____4518 = FStar_Syntax_Subst.compress head  in
          uu____4518.FStar_Syntax_Syntax.n  in
        (match uu____4517 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4522) -> u
         | uu____4539 -> failwith "Not a flex-uvar")
  
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0  ->
    fun wl  ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x  in
        let t_x' = FStar_Syntax_Subst.subst' s t_x  in
        let uu____4575 =
          let uu____4576 = FStar_Syntax_Subst.compress t_x'  in
          uu____4576.FStar_Syntax_Syntax.n  in
        match uu____4575 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____4581 -> false  in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____4597 -> true  in
      let uu____4599 = FStar_Syntax_Util.head_and_args t0  in
      match uu____4599 with
      | (head,args) ->
          let uu____4646 =
            let uu____4647 = FStar_Syntax_Subst.compress head  in
            uu____4647.FStar_Syntax_Syntax.n  in
          (match uu____4646 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4655)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,uu____4671) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4712 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               (match uu____4712 with
                | (gamma_aff,new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____4739 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff
                            in
                         let uu____4743 =
                           let uu____4750 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma
                              in
                           let uu____4759 =
                             let uu____4762 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             FStar_Syntax_Util.arrow dom_binders uu____4762
                              in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____4750
                             uu____4759
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta
                            in
                         (match uu____4743 with
                          | (v,t_v,wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____4798  ->
                                     match uu____4798 with
                                     | (x,i) ->
                                         let uu____4817 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____4817, i)) dom_binders
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
                                    (fun uu____4849  ->
                                       match uu____4849 with
                                       | (a,i) ->
                                           let uu____4868 =
                                             FStar_Syntax_Subst.subst' s a
                                              in
                                           (uu____4868, i)) args_sol
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    FStar_Pervasives_Native.None
                                    t0.FStar_Syntax_Syntax.pos
                                   in
                                (t, wl1))))))
           | uu____4880 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
  
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t  ->
    let uu____4892 = FStar_Syntax_Util.head_and_args t  in
    match uu____4892 with
    | (head,args) ->
        let uu____4935 =
          let uu____4936 = FStar_Syntax_Subst.compress head  in
          uu____4936.FStar_Syntax_Syntax.n  in
        (match uu____4935 with
         | FStar_Syntax_Syntax.Tm_uvar (uv,s) -> (t, uv, args)
         | uu____4957 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t  ->
    fun wl  ->
      let uu____4978 = ensure_no_uvar_subst t wl  in
      match uu____4978 with
      | (t1,wl1) ->
          let uu____4989 = destruct_flex_t' t1  in (uu____4989, wl1)
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5006 =
          let uu____5029 =
            let uu____5030 = FStar_Syntax_Subst.compress k  in
            uu____5030.FStar_Syntax_Syntax.n  in
          match uu____5029 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5112 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5112)
              else
                (let uu____5147 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5147 with
                 | (ys',t1,uu____5180) ->
                     let uu____5185 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5185))
          | uu____5224 ->
              let uu____5225 =
                let uu____5230 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5230)  in
              ((ys, t), uu____5225)
           in
        match uu____5006 with
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
                 let uu____5325 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5325 c  in
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
               (let uu____5403 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5403
                then
                  let uu____5408 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5410 = print_ctx_uvar uv  in
                  let uu____5412 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5408 uu____5410 uu____5412
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5421 =
                   let uu____5423 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5423  in
                 let uu____5426 =
                   let uu____5429 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5429
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5421 uu____5426 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail uu____5462 =
               let uu____5463 =
                 let uu____5465 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5467 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5465 uu____5467
                  in
               failwith uu____5463  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5533  ->
                       match uu____5533 with
                       | (a,i) ->
                           let uu____5554 =
                             let uu____5555 = FStar_Syntax_Subst.compress a
                                in
                             uu____5555.FStar_Syntax_Syntax.n  in
                           (match uu____5554 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5581 -> (fail (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5591 =
                 let uu____5593 = is_flex g  in Prims.op_Negation uu____5593
                  in
               if uu____5591
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____5602 = destruct_flex_t g wl  in
                  match uu____5602 with
                  | ((uu____5607,uv1,args),wl1) ->
                      ((let uu____5612 = args_as_binders args  in
                        assign_solution uu____5612 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___731_5614 = wl1  in
              {
                attempting = (uu___731_5614.attempting);
                wl_deferred = (uu___731_5614.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___731_5614.defer_ok);
                smt_ok = (uu___731_5614.smt_ok);
                umax_heuristic_ok = (uu___731_5614.umax_heuristic_ok);
                tcenv = (uu___731_5614.tcenv);
                wl_implicits = (uu___731_5614.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5639 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5639
         then
           let uu____5644 = FStar_Util.string_of_int pid  in
           let uu____5646 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5644 uu____5646
         else ());
        commit sol;
        (let uu___739_5652 = wl  in
         {
           attempting = (uu___739_5652.attempting);
           wl_deferred = (uu___739_5652.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___739_5652.defer_ok);
           smt_ok = (uu___739_5652.smt_ok);
           umax_heuristic_ok = (uu___739_5652.umax_heuristic_ok);
           tcenv = (uu___739_5652.tcenv);
           wl_implicits = (uu___739_5652.wl_implicits)
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
          (let uu____5688 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5688
           then
             let uu____5693 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5697 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5693 uu____5697
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
        let uu____5724 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5724 FStar_Util.set_elements  in
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
      let uu____5764 = occurs uk t  in
      match uu____5764 with
      | (uvars,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5803 =
                 let uu____5805 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5807 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5805 uu____5807
                  in
               FStar_Pervasives_Native.Some uu____5803)
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
          let uu____5918 = FStar_Syntax_Syntax.bv_eq b b'  in
          if uu____5918
          then
            let uu____5929 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5929 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5980 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6037  ->
             match uu____6037 with
             | (x,uu____6049) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6067 = FStar_List.last bs  in
      match uu____6067 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6091) ->
          let uu____6102 =
            FStar_Util.prefix_until
              (fun uu___18_6117  ->
                 match uu___18_6117 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6120 -> false) g
             in
          (match uu____6102 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6134,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6171 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6171 with
        | (pfx,uu____6181) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6193 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6193 with
             | (uu____6201,src',wl1) ->
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
                 | uu____6315 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6316 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6380  ->
                  fun uu____6381  ->
                    match (uu____6380, uu____6381) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6484 =
                          let uu____6486 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6486
                           in
                        if uu____6484
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6520 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6520
                           then
                             let uu____6537 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6537)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6316 with | (isect,uu____6587) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu6623 'uuuuuu6624 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6623) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6624) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6682  ->
              fun uu____6683  ->
                match (uu____6682, uu____6683) with
                | ((a,uu____6702),(b,uu____6704)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu6720 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6720) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6751  ->
           match uu____6751 with
           | (y,uu____6758) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu6768 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6768) Prims.list ->
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
                   let uu____6930 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6930
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6963 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7015 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7059 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7080 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7088  ->
    match uu___19_7088 with
    | MisMatch (d1,d2) ->
        let uu____7100 =
          let uu____7102 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7104 =
            let uu____7106 =
              let uu____7108 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7108 ")"  in
            Prims.op_Hat ") (" uu____7106  in
          Prims.op_Hat uu____7102 uu____7104  in
        Prims.op_Hat "MisMatch (" uu____7100
    | HeadMatch u ->
        let uu____7115 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7115
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7124  ->
    match uu___20_7124 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7141 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7156 =
            (let uu____7162 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7164 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7162 = uu____7164) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7156 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7173 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7173 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7184 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7208 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7218 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7237 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7237
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7238 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7239 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7240 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7253 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7267 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7291) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7297,uu____7298) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7340) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7365;
             FStar_Syntax_Syntax.index = uu____7366;
             FStar_Syntax_Syntax.sort = t2;_},uu____7368)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7376 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7377 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7378 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7393 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7400 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7420 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7420
  
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
           { FStar_Syntax_Syntax.blob = uu____7439;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7440;
             FStar_Syntax_Syntax.ltyp = uu____7441;
             FStar_Syntax_Syntax.rng = uu____7442;_},uu____7443)
            ->
            let uu____7454 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7454 t21
        | (uu____7455,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7456;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7457;
             FStar_Syntax_Syntax.ltyp = uu____7458;
             FStar_Syntax_Syntax.rng = uu____7459;_})
            ->
            let uu____7470 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7470
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7473 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____7473
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7484 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7484
            then FullMatch
            else
              (let uu____7489 =
                 let uu____7498 =
                   let uu____7501 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7501  in
                 let uu____7502 =
                   let uu____7505 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7505  in
                 (uu____7498, uu____7502)  in
               MisMatch uu____7489)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7511),FStar_Syntax_Syntax.Tm_uinst (g,uu____7513)) ->
            let uu____7522 = head_matches env f g  in
            FStar_All.pipe_right uu____7522 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7523) -> HeadMatch true
        | (uu____7525,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7529 = FStar_Const.eq_const c d  in
            if uu____7529
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7539),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7541)) ->
            let uu____7574 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7574
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7584),FStar_Syntax_Syntax.Tm_refine (y,uu____7586)) ->
            let uu____7595 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7595 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7597),uu____7598) ->
            let uu____7603 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7603 head_match
        | (uu____7604,FStar_Syntax_Syntax.Tm_refine (x,uu____7606)) ->
            let uu____7611 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7611 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7612,FStar_Syntax_Syntax.Tm_type
           uu____7613) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7615,FStar_Syntax_Syntax.Tm_arrow uu____7616) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____7647),FStar_Syntax_Syntax.Tm_app (head',uu____7649))
            ->
            let uu____7698 = head_matches env head head'  in
            FStar_All.pipe_right uu____7698 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____7700),uu____7701) ->
            let uu____7726 = head_matches env head t21  in
            FStar_All.pipe_right uu____7726 head_match
        | (uu____7727,FStar_Syntax_Syntax.Tm_app (head,uu____7729)) ->
            let uu____7754 = head_matches env t11 head  in
            FStar_All.pipe_right uu____7754 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7755,FStar_Syntax_Syntax.Tm_let
           uu____7756) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7784,FStar_Syntax_Syntax.Tm_match uu____7785) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7831,FStar_Syntax_Syntax.Tm_abs
           uu____7832) -> HeadMatch true
        | uu____7870 ->
            let uu____7875 =
              let uu____7884 = delta_depth_of_term env t11  in
              let uu____7887 = delta_depth_of_term env t21  in
              (uu____7884, uu____7887)  in
            MisMatch uu____7875
  
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
              let uu____7956 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7956  in
            (let uu____7958 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7958
             then
               let uu____7963 = FStar_Syntax_Print.term_to_string t  in
               let uu____7965 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7963 uu____7965
             else ());
            (let uu____7970 =
               let uu____7971 = FStar_Syntax_Util.un_uinst head  in
               uu____7971.FStar_Syntax_Syntax.n  in
             match uu____7970 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7977 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7977 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7991 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7991
                        then
                          let uu____7996 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7996
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8001 ->
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
                      let uu____8019 =
                        let uu____8021 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8021 = FStar_Syntax_Util.Equal  in
                      if uu____8019
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8028 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8028
                          then
                            let uu____8033 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8035 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8033
                              uu____8035
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8040 -> FStar_Pervasives_Native.None)
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
            (let uu____8192 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8192
             then
               let uu____8197 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8199 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8201 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8197
                 uu____8199 uu____8201
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8229 =
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
               match uu____8229 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8277 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8277 with
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
                  uu____8315),uu____8316)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8337 =
                      let uu____8346 = maybe_inline t11  in
                      let uu____8349 = maybe_inline t21  in
                      (uu____8346, uu____8349)  in
                    match uu____8337 with
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
                 (uu____8392,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8393))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8414 =
                      let uu____8423 = maybe_inline t11  in
                      let uu____8426 = maybe_inline t21  in
                      (uu____8423, uu____8426)  in
                    match uu____8414 with
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
             | MisMatch uu____8481 -> fail n_delta r t11 t21
             | uu____8490 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8505 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8505
           then
             let uu____8510 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8512 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8514 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8522 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8539 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8539
                    (fun uu____8574  ->
                       match uu____8574 with
                       | (t11,t21) ->
                           let uu____8582 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8584 =
                             let uu____8586 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8586  in
                           Prims.op_Hat uu____8582 uu____8584))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8510 uu____8512 uu____8514 uu____8522
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8603 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8603 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8618  ->
    match uu___21_8618 with
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
      let uu___1228_8667 = p  in
      let uu____8670 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8671 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1228_8667.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8670;
        FStar_TypeChecker_Common.relation =
          (uu___1228_8667.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8671;
        FStar_TypeChecker_Common.element =
          (uu___1228_8667.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1228_8667.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1228_8667.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1228_8667.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1228_8667.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1228_8667.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8686 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8686
            (fun uu____8691  -> FStar_TypeChecker_Common.TProb uu____8691)
      | FStar_TypeChecker_Common.CProb uu____8692 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8715 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8715 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8723 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8723 with
           | (lh,lhs_args) ->
               let uu____8770 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8770 with
                | (rh,rhs_args) ->
                    let uu____8817 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8830,FStar_Syntax_Syntax.Tm_uvar uu____8831)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8920 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8947,uu____8948)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8963,FStar_Syntax_Syntax.Tm_uvar uu____8964)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8979,FStar_Syntax_Syntax.Tm_arrow uu____8980)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_9010 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_9010.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_9010.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_9010.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_9010.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_9010.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_9010.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_9010.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_9010.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_9010.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9013,FStar_Syntax_Syntax.Tm_type uu____9014)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_9030 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_9030.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_9030.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_9030.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_9030.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_9030.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_9030.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_9030.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_9030.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_9030.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9033,FStar_Syntax_Syntax.Tm_uvar uu____9034)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_9050 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_9050.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_9050.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_9050.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_9050.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_9050.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_9050.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_9050.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_9050.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_9050.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9053,FStar_Syntax_Syntax.Tm_uvar uu____9054)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9069,uu____9070)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9085,FStar_Syntax_Syntax.Tm_uvar uu____9086)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9101,uu____9102) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8817 with
                     | (rank,tp1) ->
                         let uu____9115 =
                           FStar_All.pipe_right
                             (let uu___1299_9119 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1299_9119.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1299_9119.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1299_9119.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1299_9119.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1299_9119.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1299_9119.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1299_9119.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1299_9119.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1299_9119.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9122  ->
                                FStar_TypeChecker_Common.TProb uu____9122)
                            in
                         (rank, uu____9115))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9126 =
            FStar_All.pipe_right
              (let uu___1303_9130 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1303_9130.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1303_9130.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1303_9130.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1303_9130.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1303_9130.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1303_9130.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1303_9130.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1303_9130.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1303_9130.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9133  -> FStar_TypeChecker_Common.CProb uu____9133)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9126)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9193 probs =
      match uu____9193 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9274 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9295 = rank wl.tcenv hd  in
               (match uu____9295 with
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
                      (let uu____9356 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9361 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9361)
                          in
                       if uu____9356
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
          let uu____9434 = FStar_Syntax_Util.head_and_args t  in
          match uu____9434 with
          | (hd,uu____9453) ->
              let uu____9478 =
                let uu____9479 = FStar_Syntax_Subst.compress hd  in
                uu____9479.FStar_Syntax_Syntax.n  in
              (match uu____9478 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9484) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9519  ->
                           match uu____9519 with
                           | (y,uu____9528) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9551  ->
                                       match uu____9551 with
                                       | (x,uu____9560) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9565 -> false)
           in
        let uu____9567 = rank tcenv p  in
        match uu____9567 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9576 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9657 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9676 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9695 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9712 = FStar_Thunk.mkv s  in UFailed uu____9712 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9727 = mklstr s  in UFailed uu____9727 
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
                        let uu____9778 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9778 with
                        | (k,uu____9786) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9799 -> false)))
            | uu____9801 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9853 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9861 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9861 = Prims.int_zero))
                           in
                        if uu____9853 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____9882 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9890 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9890 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9882)
               in
            let uu____9894 = filter u12  in
            let uu____9897 = filter u22  in (uu____9894, uu____9897)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9932 = filter_out_common_univs us1 us2  in
                   (match uu____9932 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9992 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9992 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9995 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10012  ->
                               let uu____10013 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10015 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10013 uu____10015))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10041 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10041 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10067 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10067 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10070 ->
                   ufailed_thunk
                     (fun uu____10081  ->
                        let uu____10082 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10084 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10082 uu____10084 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10087,uu____10088) ->
              let uu____10090 =
                let uu____10092 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10094 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10092 uu____10094
                 in
              failwith uu____10090
          | (FStar_Syntax_Syntax.U_unknown ,uu____10097) ->
              let uu____10098 =
                let uu____10100 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10102 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10100 uu____10102
                 in
              failwith uu____10098
          | (uu____10105,FStar_Syntax_Syntax.U_bvar uu____10106) ->
              let uu____10108 =
                let uu____10110 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10112 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10110 uu____10112
                 in
              failwith uu____10108
          | (uu____10115,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10116 =
                let uu____10118 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10120 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10118 uu____10120
                 in
              failwith uu____10116
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10125 =
                let uu____10127 = FStar_Ident.text_of_id x  in
                let uu____10129 = FStar_Ident.text_of_id y  in
                uu____10127 = uu____10129  in
              if uu____10125
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
              let uu____10173 = occurs_univ v1 u3  in
              if uu____10173
              then
                let uu____10176 =
                  let uu____10178 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10180 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10178 uu____10180
                   in
                try_umax_components u11 u21 uu____10176
              else
                (let uu____10185 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10185)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10197 = occurs_univ v1 u3  in
              if uu____10197
              then
                let uu____10200 =
                  let uu____10202 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10204 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10202 uu____10204
                   in
                try_umax_components u11 u21 uu____10200
              else
                (let uu____10209 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10209)
          | (FStar_Syntax_Syntax.U_max uu____10210,uu____10211) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10219 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10219
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10225,FStar_Syntax_Syntax.U_max uu____10226) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10234 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10234
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10240,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10242,FStar_Syntax_Syntax.U_name uu____10243) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10245) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10247) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10249,FStar_Syntax_Syntax.U_succ uu____10250) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10252,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10359 = bc1  in
      match uu____10359 with
      | (bs1,mk_cod1) ->
          let uu____10403 = bc2  in
          (match uu____10403 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10514 = aux xs ys  in
                     (match uu____10514 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10597 =
                       let uu____10604 = mk_cod1 xs  in ([], uu____10604)  in
                     let uu____10607 =
                       let uu____10614 = mk_cod2 ys  in ([], uu____10614)  in
                     (uu____10597, uu____10607)
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
                  let uu____10683 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10683 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10686 =
                    let uu____10687 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10687 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10686
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10692 = has_type_guard t1 t2  in (uu____10692, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10693 = has_type_guard t2 t1  in (uu____10693, wl)
  
let is_flex_pat :
  'uuuuuu10703 'uuuuuu10704 'uuuuuu10705 .
    ('uuuuuu10703 * 'uuuuuu10704 * 'uuuuuu10705 Prims.list) -> Prims.bool
  =
  fun uu___22_10719  ->
    match uu___22_10719 with
    | (uu____10728,uu____10729,[]) -> true
    | uu____10733 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10766 = f  in
      match uu____10766 with
      | (uu____10773,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10774;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10775;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10778;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10779;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10780;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10781;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10851  ->
                 match uu____10851 with
                 | (y,uu____10860) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11014 =
                  let uu____11029 =
                    let uu____11032 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11032  in
                  ((FStar_List.rev pat_binders), uu____11029)  in
                FStar_Pervasives_Native.Some uu____11014
            | (uu____11065,[]) ->
                let uu____11096 =
                  let uu____11111 =
                    let uu____11114 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11114  in
                  ((FStar_List.rev pat_binders), uu____11111)  in
                FStar_Pervasives_Native.Some uu____11096
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11205 =
                  let uu____11206 = FStar_Syntax_Subst.compress a  in
                  uu____11206.FStar_Syntax_Syntax.n  in
                (match uu____11205 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11226 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11226
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1631_11256 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1631_11256.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1631_11256.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11260 =
                            let uu____11261 =
                              let uu____11268 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11268)  in
                            FStar_Syntax_Syntax.NT uu____11261  in
                          [uu____11260]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1637_11284 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1637_11284.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1637_11284.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11285 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11325 =
                  let uu____11332 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11332  in
                (match uu____11325 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11391 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11416 ->
               let uu____11417 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11417 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11713 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11713
       then
         let uu____11718 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11718
       else ());
      (let uu____11724 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11724
       then
         let uu____11729 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11729
       else ());
      (let uu____11734 = next_prob probs  in
       match uu____11734 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1664_11761 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1664_11761.wl_deferred);
               ctr = (uu___1664_11761.ctr);
               defer_ok = (uu___1664_11761.defer_ok);
               smt_ok = (uu___1664_11761.smt_ok);
               umax_heuristic_ok = (uu___1664_11761.umax_heuristic_ok);
               tcenv = (uu___1664_11761.tcenv);
               wl_implicits = (uu___1664_11761.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11770 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11770
                 then
                   let uu____11773 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____11773
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
                       (let uu____11780 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd
                            probs1
                           in
                        solve env uu____11780)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1676_11786 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1676_11786.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1676_11786.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1676_11786.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1676_11786.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1676_11786.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1676_11786.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1676_11786.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1676_11786.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1676_11786.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11811 ->
                let uu____11821 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11886  ->
                          match uu____11886 with
                          | (c,uu____11896,uu____11897) -> c < probs.ctr))
                   in
                (match uu____11821 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11945 =
                            let uu____11950 =
                              FStar_List.map
                                (fun uu____11971  ->
                                   match uu____11971 with
                                   | (uu____11987,x,y) ->
                                       let uu____11998 = FStar_Thunk.force x
                                          in
                                       (uu____11998, y)) probs.wl_deferred
                               in
                            (uu____11950, (probs.wl_implicits))  in
                          Success uu____11945
                      | uu____12002 ->
                          let uu____12012 =
                            let uu___1694_12013 = probs  in
                            let uu____12014 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12035  ->
                                      match uu____12035 with
                                      | (uu____12043,uu____12044,y) -> y))
                               in
                            {
                              attempting = uu____12014;
                              wl_deferred = rest;
                              ctr = (uu___1694_12013.ctr);
                              defer_ok = (uu___1694_12013.defer_ok);
                              smt_ok = (uu___1694_12013.smt_ok);
                              umax_heuristic_ok =
                                (uu___1694_12013.umax_heuristic_ok);
                              tcenv = (uu___1694_12013.tcenv);
                              wl_implicits = (uu___1694_12013.wl_implicits)
                            }  in
                          solve env uu____12012))))

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
            let uu____12053 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12053 with
            | USolved wl1 ->
                let uu____12055 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12055
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12058 = defer_lit "" orig wl1  in
                solve env uu____12058

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
                  let uu____12109 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12109 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12112 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12125;
                  FStar_Syntax_Syntax.vars = uu____12126;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12129;
                  FStar_Syntax_Syntax.vars = uu____12130;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12143,uu____12144) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12152,FStar_Syntax_Syntax.Tm_uinst uu____12153) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12161 -> USolved wl

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
            ((let uu____12172 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12172
              then
                let uu____12177 = prob_to_string env orig  in
                let uu____12179 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12177 uu____12179
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
               let uu____12272 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12272 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12327 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12327
                then
                  let uu____12332 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12334 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12332 uu____12334
                else ());
               (let uu____12339 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12339 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12385 = eq_prob t1 t2 wl2  in
                         (match uu____12385 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12406 ->
                         let uu____12415 = eq_prob t1 t2 wl2  in
                         (match uu____12415 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12465 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12480 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12481 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12480, uu____12481)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12486 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12487 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12486, uu____12487)
                            in
                         (match uu____12465 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12518 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12518 with
                                | (t1_hd,t1_args) ->
                                    let uu____12563 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12563 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12629 =
                                              let uu____12636 =
                                                let uu____12647 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12647 :: t1_args  in
                                              let uu____12664 =
                                                let uu____12673 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12673 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12722  ->
                                                   fun uu____12723  ->
                                                     fun uu____12724  ->
                                                       match (uu____12722,
                                                               uu____12723,
                                                               uu____12724)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12774),
                                                          (a2,uu____12776))
                                                           ->
                                                           let uu____12813 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12813
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12636
                                                uu____12664
                                               in
                                            match uu____12629 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1848_12839 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1848_12839.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1848_12839.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1848_12839.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12850 =
                                                  solve env1 wl'  in
                                                (match uu____12850 with
                                                 | Success (uu____12853,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1857_12857
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1857_12857.attempting);
                                                            wl_deferred =
                                                              (uu___1857_12857.wl_deferred);
                                                            ctr =
                                                              (uu___1857_12857.ctr);
                                                            defer_ok =
                                                              (uu___1857_12857.defer_ok);
                                                            smt_ok =
                                                              (uu___1857_12857.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1857_12857.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1857_12857.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12858 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12890 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12890 with
                                | (t1_base,p1_opt) ->
                                    let uu____12926 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12926 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13025 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13025
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
                                               let uu____13078 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13078
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
                                               let uu____13110 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13110
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
                                               let uu____13142 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13142
                                           | uu____13145 -> t_base  in
                                         let uu____13162 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13162 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13176 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13176, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13183 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13183 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13219 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13219 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13255 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13255
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
                              let uu____13279 = combine t11 t21 wl2  in
                              (match uu____13279 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13312 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13312
                                     then
                                       let uu____13317 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13317
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13359 ts1 =
               match uu____13359 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13422 = pairwise out t wl2  in
                        (match uu____13422 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13458 =
               let uu____13469 = FStar_List.hd ts  in (uu____13469, [], wl1)
                in
             let uu____13478 = FStar_List.tl ts  in
             aux uu____13458 uu____13478  in
           let uu____13485 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13485 with
           | (this_flex,this_rigid) ->
               let uu____13511 =
                 let uu____13512 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13512.FStar_Syntax_Syntax.n  in
               (match uu____13511 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13537 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13537
                    then
                      let uu____13540 = destruct_flex_t this_flex wl  in
                      (match uu____13540 with
                       | (flex,wl1) ->
                           let uu____13547 = quasi_pattern env flex  in
                           (match uu____13547 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____13566 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13566
                                  then
                                    let uu____13571 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13571
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13578 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1959_13581 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1959_13581.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1959_13581.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1959_13581.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1959_13581.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1959_13581.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1959_13581.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1959_13581.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1959_13581.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1959_13581.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13578)
                | uu____13582 ->
                    ((let uu____13584 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13584
                      then
                        let uu____13589 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13589
                      else ());
                     (let uu____13594 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13594 with
                      | (u,_args) ->
                          let uu____13637 =
                            let uu____13638 = FStar_Syntax_Subst.compress u
                               in
                            uu____13638.FStar_Syntax_Syntax.n  in
                          (match uu____13637 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____13666 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13666 with
                                 | (u',uu____13685) ->
                                     let uu____13710 =
                                       let uu____13711 = whnf env u'  in
                                       uu____13711.FStar_Syntax_Syntax.n  in
                                     (match uu____13710 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13733 -> false)
                                  in
                               let uu____13735 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13758  ->
                                         match uu___23_13758 with
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
                                              | uu____13772 -> false)
                                         | uu____13776 -> false))
                                  in
                               (match uu____13735 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13791 = whnf env this_rigid
                                         in
                                      let uu____13792 =
                                        FStar_List.collect
                                          (fun uu___24_13798  ->
                                             match uu___24_13798 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13804 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13804]
                                             | uu____13808 -> [])
                                          bounds_probs
                                         in
                                      uu____13791 :: uu____13792  in
                                    let uu____13809 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13809 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13842 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13857 =
                                               let uu____13858 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13858.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13857 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13870 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13870)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13881 -> bound  in
                                           let uu____13882 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13882)  in
                                         (match uu____13842 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13917 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13917
                                                then
                                                  let wl'1 =
                                                    let uu___2019_13923 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2019_13923.wl_deferred);
                                                      ctr =
                                                        (uu___2019_13923.ctr);
                                                      defer_ok =
                                                        (uu___2019_13923.defer_ok);
                                                      smt_ok =
                                                        (uu___2019_13923.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2019_13923.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2019_13923.tcenv);
                                                      wl_implicits =
                                                        (uu___2019_13923.wl_implicits)
                                                    }  in
                                                  let uu____13924 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13924
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13930 =
                                                  solve_t env eq_prob
                                                    (let uu___2024_13932 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2024_13932.wl_deferred);
                                                       ctr =
                                                         (uu___2024_13932.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2024_13932.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2024_13932.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2024_13932.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13930 with
                                                | Success (uu____13934,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2030_13937 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2030_13937.wl_deferred);
                                                        ctr =
                                                          (uu___2030_13937.ctr);
                                                        defer_ok =
                                                          (uu___2030_13937.defer_ok);
                                                        smt_ok =
                                                          (uu___2030_13937.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2030_13937.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2030_13937.tcenv);
                                                        wl_implicits =
                                                          (uu___2030_13937.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2033_13939 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2033_13939.attempting);
                                                        wl_deferred =
                                                          (uu___2033_13939.wl_deferred);
                                                        ctr =
                                                          (uu___2033_13939.ctr);
                                                        defer_ok =
                                                          (uu___2033_13939.defer_ok);
                                                        smt_ok =
                                                          (uu___2033_13939.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2033_13939.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2033_13939.tcenv);
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
                                                    let uu____13955 =
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
                                                    ((let uu____13967 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13967
                                                      then
                                                        let uu____13972 =
                                                          let uu____13974 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13974
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13972
                                                      else ());
                                                     (let uu____13987 =
                                                        let uu____14002 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14002)
                                                         in
                                                      match uu____13987 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14024))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14050 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14050
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
                                                                  let uu____14070
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14070))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14095 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14095
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
                                                                    let uu____14115
                                                                    =
                                                                    let uu____14120
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14120
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14115
                                                                    [] wl2
                                                                     in
                                                                  let uu____14126
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14126))))
                                                      | uu____14127 ->
                                                          let uu____14142 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14142 p)))))))
                           | uu____14149 when flip ->
                               let uu____14150 =
                                 let uu____14152 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14154 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14152 uu____14154
                                  in
                               failwith uu____14150
                           | uu____14157 ->
                               let uu____14158 =
                                 let uu____14160 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14162 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14160 uu____14162
                                  in
                               failwith uu____14158)))))

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
                      (fun uu____14198  ->
                         match uu____14198 with
                         | (x,i) ->
                             let uu____14217 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14217, i)) bs_lhs
                     in
                  let uu____14220 = lhs  in
                  match uu____14220 with
                  | (uu____14221,u_lhs,uu____14223) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14320 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14330 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14330, univ)
                             in
                          match uu____14320 with
                          | (k,univ) ->
                              let uu____14337 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14337 with
                               | (uu____14354,u,wl3) ->
                                   let uu____14357 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14357, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14383 =
                              let uu____14396 =
                                let uu____14407 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14407 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14458  ->
                                   fun uu____14459  ->
                                     match (uu____14458, uu____14459) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14560 =
                                           let uu____14567 =
                                             let uu____14570 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14570
                                              in
                                           copy_uvar u_lhs [] uu____14567 wl2
                                            in
                                         (match uu____14560 with
                                          | (uu____14599,t_a,wl3) ->
                                              let uu____14602 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14602 with
                                               | (uu____14621,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14396
                                ([], wl1)
                               in
                            (match uu____14383 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2144_14677 = ct  in
                                   let uu____14678 =
                                     let uu____14681 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14681
                                      in
                                   let uu____14696 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2144_14677.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2144_14677.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14678;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14696;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2144_14677.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2147_14714 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2147_14714.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2147_14714.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14717 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____14717 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14755 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14755 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14766 =
                                          let uu____14771 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14771)  in
                                        TERM uu____14766  in
                                      let uu____14772 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14772 with
                                       | (sub_prob,wl3) ->
                                           let uu____14786 =
                                             let uu____14787 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14787
                                              in
                                           solve env uu____14786))
                             | (x,imp)::formals2 ->
                                 let uu____14809 =
                                   let uu____14816 =
                                     let uu____14819 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14819
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14816 wl1
                                    in
                                 (match uu____14809 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14840 =
                                          let uu____14843 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14843
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14840 u_x
                                         in
                                      let uu____14844 =
                                        let uu____14847 =
                                          let uu____14850 =
                                            let uu____14851 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14851, imp)  in
                                          [uu____14850]  in
                                        FStar_List.append bs_terms
                                          uu____14847
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14844 formals2 wl2)
                              in
                           let uu____14878 = occurs_check u_lhs arrow  in
                           (match uu____14878 with
                            | (uu____14891,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14907 =
                                    mklstr
                                      (fun uu____14912  ->
                                         let uu____14913 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14913)
                                     in
                                  giveup_or_defer env orig wl uu____14907
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
              (let uu____14946 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14946
               then
                 let uu____14951 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14954 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14951 (rel_to_string (p_rel orig)) uu____14954
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15085 = rhs wl1 scope env1 subst  in
                     (match uu____15085 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15108 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15108
                            then
                              let uu____15113 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15113
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15191 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15191 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2217_15193 = hd1  in
                       let uu____15194 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2217_15193.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2217_15193.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15194
                       }  in
                     let hd21 =
                       let uu___2220_15198 = hd2  in
                       let uu____15199 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2220_15198.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2220_15198.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15199
                       }  in
                     let uu____15202 =
                       let uu____15207 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15207
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15202 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15230 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15230
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15237 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15237 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15309 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15309
                                  in
                               ((let uu____15327 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15327
                                 then
                                   let uu____15332 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15334 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15332
                                     uu____15334
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15369 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15405 = aux wl [] env [] bs1 bs2  in
               match uu____15405 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15464 = attempt sub_probs wl2  in
                   solve env1 uu____15464)

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
            let uu___2258_15484 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2258_15484.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2258_15484.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15496 = try_solve env wl'  in
          match uu____15496 with
          | Success (uu____15497,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2267_15501 = wl  in
                  {
                    attempting = (uu___2267_15501.attempting);
                    wl_deferred = (uu___2267_15501.wl_deferred);
                    ctr = (uu___2267_15501.ctr);
                    defer_ok = (uu___2267_15501.defer_ok);
                    smt_ok = (uu___2267_15501.smt_ok);
                    umax_heuristic_ok = (uu___2267_15501.umax_heuristic_ok);
                    tcenv = (uu___2267_15501.tcenv);
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
        (let uu____15510 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15510 wl)

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
              let uu____15524 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15524 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15558 = lhs1  in
              match uu____15558 with
              | (uu____15561,ctx_u,uu____15563) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15571 ->
                        let uu____15572 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15572 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15621 = quasi_pattern env1 lhs1  in
              match uu____15621 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15655) ->
                  let uu____15660 = lhs1  in
                  (match uu____15660 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15675 = occurs_check ctx_u rhs1  in
                       (match uu____15675 with
                        | (uvars,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15726 =
                                let uu____15734 =
                                  let uu____15736 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15736
                                   in
                                FStar_Util.Inl uu____15734  in
                              (uu____15726, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15764 =
                                 let uu____15766 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15766  in
                               if uu____15764
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15793 =
                                    let uu____15801 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15801  in
                                  let uu____15807 =
                                    restrict_all_uvars ctx_u uvars wl1  in
                                  (uu____15793, uu____15807)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15851 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15851 with
              | (rhs_hd,args) ->
                  let uu____15894 = FStar_Util.prefix args  in
                  (match uu____15894 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15966 = lhs1  in
                       (match uu____15966 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15970 =
                              let uu____15981 =
                                let uu____15988 =
                                  let uu____15991 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15991
                                   in
                                copy_uvar u_lhs [] uu____15988 wl1  in
                              match uu____15981 with
                              | (uu____16018,t_last_arg,wl2) ->
                                  let uu____16021 =
                                    let uu____16028 =
                                      let uu____16029 =
                                        let uu____16038 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16038]  in
                                      FStar_List.append bs_lhs uu____16029
                                       in
                                    copy_uvar u_lhs uu____16028 t_res_lhs wl2
                                     in
                                  (match uu____16021 with
                                   | (uu____16073,lhs',wl3) ->
                                       let uu____16076 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16076 with
                                        | (uu____16093,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15970 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16114 =
                                     let uu____16115 =
                                       let uu____16120 =
                                         let uu____16121 =
                                           let uu____16124 =
                                             let uu____16129 =
                                               let uu____16130 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16130]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16129
                                              in
                                           uu____16124
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16121
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16120)  in
                                     TERM uu____16115  in
                                   [uu____16114]  in
                                 let uu____16155 =
                                   let uu____16162 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16162 with
                                   | (p1,wl3) ->
                                       let uu____16182 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16182 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16155 with
                                  | (sub_probs,wl3) ->
                                      let uu____16214 =
                                        let uu____16215 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16215  in
                                      solve env1 uu____16214))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16249 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16249 with
                | (uu____16267,args) ->
                    (match args with | [] -> false | uu____16303 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16322 =
                  let uu____16323 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16323.FStar_Syntax_Syntax.n  in
                match uu____16322 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16327 -> true
                | uu____16343 -> false  in
              let uu____16345 = quasi_pattern env1 lhs1  in
              match uu____16345 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16364  ->
                         let uu____16365 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16365)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16374 = is_app rhs1  in
                  if uu____16374
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16379 = is_arrow rhs1  in
                     if uu____16379
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16392  ->
                               let uu____16393 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16393)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16397 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16397
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16403 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16403
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16408 = lhs  in
                (match uu____16408 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16412 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16412 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16430 =
                              let uu____16434 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16434
                               in
                            FStar_All.pipe_right uu____16430
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16455 = occurs_check ctx_uv rhs1  in
                          (match uu____16455 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16484 =
                                   let uu____16485 =
                                     let uu____16487 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16487
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16485
                                    in
                                 giveup_or_defer env orig wl uu____16484
                               else
                                 (let uu____16495 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16495
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars wl  in
                                    let uu____16502 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16502
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16518  ->
                                              let uu____16519 =
                                                names_to_string1 fvs2  in
                                              let uu____16521 =
                                                names_to_string1 fvs1  in
                                              let uu____16523 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16519 uu____16521
                                                uu____16523)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16535 ->
                          if wl.defer_ok
                          then
                            let uu____16539 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16539
                          else
                            (let uu____16544 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16544 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16570 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16570
                             | (FStar_Util.Inl msg,uu____16572) ->
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
                  let uu____16590 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16590
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16596 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16596
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16618 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16618
                else
                  (let uu____16623 =
                     let uu____16640 = quasi_pattern env lhs  in
                     let uu____16647 = quasi_pattern env rhs  in
                     (uu____16640, uu____16647)  in
                   match uu____16623 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16690 = lhs  in
                       (match uu____16690 with
                        | ({ FStar_Syntax_Syntax.n = uu____16691;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16693;_},u_lhs,uu____16695)
                            ->
                            let uu____16698 = rhs  in
                            (match uu____16698 with
                             | (uu____16699,u_rhs,uu____16701) ->
                                 let uu____16702 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16702
                                 then
                                   let uu____16709 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16709
                                 else
                                   (let uu____16712 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16712 with
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
                                        let uu____16744 =
                                          let uu____16751 =
                                            let uu____16754 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16754
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16751
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16744 with
                                         | (uu____16766,w,wl1) ->
                                             let w_app =
                                               let uu____16772 =
                                                 let uu____16777 =
                                                   FStar_List.map
                                                     (fun uu____16788  ->
                                                        match uu____16788
                                                        with
                                                        | (z,uu____16796) ->
                                                            let uu____16801 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16801) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16777
                                                  in
                                               uu____16772
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16803 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16803
                                               then
                                                 let uu____16808 =
                                                   let uu____16812 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16814 =
                                                     let uu____16818 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16820 =
                                                       let uu____16824 =
                                                         term_to_string w  in
                                                       let uu____16826 =
                                                         let uu____16830 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16839 =
                                                           let uu____16843 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16852 =
                                                             let uu____16856
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16856]
                                                              in
                                                           uu____16843 ::
                                                             uu____16852
                                                            in
                                                         uu____16830 ::
                                                           uu____16839
                                                          in
                                                       uu____16824 ::
                                                         uu____16826
                                                        in
                                                     uu____16818 ::
                                                       uu____16820
                                                      in
                                                   uu____16812 :: uu____16814
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16808
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16873 =
                                                     let uu____16878 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16878)  in
                                                   TERM uu____16873  in
                                                 let uu____16879 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16879
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16887 =
                                                        let uu____16892 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16892)
                                                         in
                                                      TERM uu____16887  in
                                                    [s1; s2])
                                                  in
                                               let uu____16893 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16893))))))
                   | uu____16894 ->
                       let uu____16911 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16911)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16965 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16965
            then
              let uu____16970 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16972 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16974 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16976 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16970 uu____16972 uu____16974 uu____16976
            else ());
           (let uu____16987 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16987 with
            | (head1,args1) ->
                let uu____17030 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17030 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17100 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17100 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17105 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17105)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17126 =
                         mklstr
                           (fun uu____17137  ->
                              let uu____17138 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17140 = args_to_string args1  in
                              let uu____17144 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17146 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17138 uu____17140 uu____17144
                                uu____17146)
                          in
                       giveup env1 uu____17126 orig
                     else
                       (let uu____17153 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17158 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17158 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17153
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2523_17162 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2523_17162.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2523_17162.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2523_17162.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2523_17162.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2523_17162.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2523_17162.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2523_17162.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2523_17162.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17172 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17172
                                    else solve env1 wl2))
                        else
                          (let uu____17177 = base_and_refinement env1 t1  in
                           match uu____17177 with
                           | (base1,refinement1) ->
                               let uu____17202 = base_and_refinement env1 t2
                                  in
                               (match uu____17202 with
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
                                           let uu____17367 =
                                             FStar_List.fold_right
                                               (fun uu____17407  ->
                                                  fun uu____17408  ->
                                                    match (uu____17407,
                                                            uu____17408)
                                                    with
                                                    | (((a1,uu____17460),
                                                        (a2,uu____17462)),
                                                       (probs,wl3)) ->
                                                        let uu____17511 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17511
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17367 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17554 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17554
                                                 then
                                                   let uu____17559 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17559
                                                 else ());
                                                (let uu____17565 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17565
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
                                                    (let uu____17592 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17592 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17608 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17608
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17616 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17616))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17641 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17641 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17657 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17657
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17665 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17665)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17693 =
                                           match uu____17693 with
                                           | (prob,reason) ->
                                               ((let uu____17710 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17710
                                                 then
                                                   let uu____17715 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17717 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17715 uu____17717
                                                 else ());
                                                (let uu____17723 =
                                                   let uu____17732 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17735 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17732, uu____17735)
                                                    in
                                                 match uu____17723 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17748 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17748 with
                                                      | (head1',uu____17766)
                                                          ->
                                                          let uu____17791 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17791
                                                           with
                                                           | (head2',uu____17809)
                                                               ->
                                                               let uu____17834
                                                                 =
                                                                 let uu____17839
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17840
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17839,
                                                                   uu____17840)
                                                                  in
                                                               (match uu____17834
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17842
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17842
                                                                    then
                                                                    let uu____17847
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17849
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17851
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17853
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17847
                                                                    uu____17849
                                                                    uu____17851
                                                                    uu____17853
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17858
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2611_17866
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2611_17866.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2611_17866.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2611_17866.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2611_17866.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2611_17866.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2611_17866.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2611_17866.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2611_17866.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17868
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17868
                                                                    then
                                                                    let uu____17873
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17873
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17878 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17890 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17890 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17898 =
                                             let uu____17899 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17899.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17898 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17904 -> false  in
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
                                          | uu____17907 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17910 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2631_17946 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2631_17946.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2631_17946.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2631_17946.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2631_17946.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2631_17946.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2631_17946.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2631_17946.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2631_17946.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18022 = destruct_flex_t scrutinee wl1  in
             match uu____18022 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18033 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18033 with
                  | (xs,pat_term,uu____18049,uu____18050) ->
                      let uu____18055 =
                        FStar_List.fold_left
                          (fun uu____18078  ->
                             fun x  ->
                               match uu____18078 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18099 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18099 with
                                    | (uu____18118,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18055 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18139 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18139 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2671_18156 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2671_18156.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2671_18156.umax_heuristic_ok);
                                    tcenv = (uu___2671_18156.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18167 = solve env1 wl'  in
                                (match uu____18167 with
                                 | Success (uu____18170,imps) ->
                                     let wl'1 =
                                       let uu___2679_18173 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2679_18173.wl_deferred);
                                         ctr = (uu___2679_18173.ctr);
                                         defer_ok =
                                           (uu___2679_18173.defer_ok);
                                         smt_ok = (uu___2679_18173.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2679_18173.umax_heuristic_ok);
                                         tcenv = (uu___2679_18173.tcenv);
                                         wl_implicits =
                                           (uu___2679_18173.wl_implicits)
                                       }  in
                                     let uu____18174 = solve env1 wl'1  in
                                     (match uu____18174 with
                                      | Success (uu____18177,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2687_18181 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2687_18181.attempting);
                                                 wl_deferred =
                                                   (uu___2687_18181.wl_deferred);
                                                 ctr = (uu___2687_18181.ctr);
                                                 defer_ok =
                                                   (uu___2687_18181.defer_ok);
                                                 smt_ok =
                                                   (uu___2687_18181.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2687_18181.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2687_18181.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18182 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18188 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18211 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18211
                 then
                   let uu____18216 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18218 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18216 uu____18218
                 else ());
                (let uu____18223 =
                   let uu____18244 =
                     let uu____18253 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18253)  in
                   let uu____18260 =
                     let uu____18269 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18269)  in
                   (uu____18244, uu____18260)  in
                 match uu____18223 with
                 | ((uu____18299,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18302;
                                   FStar_Syntax_Syntax.vars = uu____18303;_}),
                    (s,t)) ->
                     let uu____18374 =
                       let uu____18376 = is_flex scrutinee  in
                       Prims.op_Negation uu____18376  in
                     if uu____18374
                     then
                       ((let uu____18387 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18387
                         then
                           let uu____18392 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18392
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18411 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18411
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18426 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18426
                           then
                             let uu____18431 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18433 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18431 uu____18433
                           else ());
                          (let pat_discriminates uu___25_18458 =
                             match uu___25_18458 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18474;
                                  FStar_Syntax_Syntax.p = uu____18475;_},FStar_Pervasives_Native.None
                                ,uu____18476) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18490;
                                  FStar_Syntax_Syntax.p = uu____18491;_},FStar_Pervasives_Native.None
                                ,uu____18492) -> true
                             | uu____18519 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18622 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18622 with
                                       | (uu____18624,uu____18625,t') ->
                                           let uu____18643 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18643 with
                                            | (FullMatch ,uu____18655) ->
                                                true
                                            | (HeadMatch
                                               uu____18669,uu____18670) ->
                                                true
                                            | uu____18685 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18722 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18722
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18733 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18733 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18821,uu____18822) ->
                                       branches1
                                   | uu____18967 -> branches  in
                                 let uu____19022 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19031 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19031 with
                                        | (p,uu____19035,uu____19036) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19065  ->
                                      FStar_Util.Inr uu____19065) uu____19022))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19095 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19095 with
                                | (p,uu____19104,e) ->
                                    ((let uu____19123 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19123
                                      then
                                        let uu____19128 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19130 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19128 uu____19130
                                      else ());
                                     (let uu____19135 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19150  ->
                                           FStar_Util.Inr uu____19150)
                                        uu____19135)))))
                 | ((s,t),(uu____19153,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19156;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19157;_}))
                     ->
                     let uu____19226 =
                       let uu____19228 = is_flex scrutinee  in
                       Prims.op_Negation uu____19228  in
                     if uu____19226
                     then
                       ((let uu____19239 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19239
                         then
                           let uu____19244 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19244
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19263 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19263
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19278 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19278
                           then
                             let uu____19283 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19285 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19283 uu____19285
                           else ());
                          (let pat_discriminates uu___25_19310 =
                             match uu___25_19310 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19326;
                                  FStar_Syntax_Syntax.p = uu____19327;_},FStar_Pervasives_Native.None
                                ,uu____19328) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19342;
                                  FStar_Syntax_Syntax.p = uu____19343;_},FStar_Pervasives_Native.None
                                ,uu____19344) -> true
                             | uu____19371 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19474 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19474 with
                                       | (uu____19476,uu____19477,t') ->
                                           let uu____19495 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19495 with
                                            | (FullMatch ,uu____19507) ->
                                                true
                                            | (HeadMatch
                                               uu____19521,uu____19522) ->
                                                true
                                            | uu____19537 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19574 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19574
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19585 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19585 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19673,uu____19674) ->
                                       branches1
                                   | uu____19819 -> branches  in
                                 let uu____19874 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19883 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19883 with
                                        | (p,uu____19887,uu____19888) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19917  ->
                                      FStar_Util.Inr uu____19917) uu____19874))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19947 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19947 with
                                | (p,uu____19956,e) ->
                                    ((let uu____19975 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19975
                                      then
                                        let uu____19980 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19982 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19980 uu____19982
                                      else ());
                                     (let uu____19987 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20002  ->
                                           FStar_Util.Inr uu____20002)
                                        uu____19987)))))
                 | uu____20003 ->
                     ((let uu____20025 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20025
                       then
                         let uu____20030 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20032 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20030 uu____20032
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20078 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20078
            then
              let uu____20083 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20085 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20087 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20089 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20083 uu____20085 uu____20087 uu____20089
            else ());
           (let uu____20094 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20094 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20125,uu____20126) ->
                     let rec may_relate head =
                       let uu____20154 =
                         let uu____20155 = FStar_Syntax_Subst.compress head
                            in
                         uu____20155.FStar_Syntax_Syntax.n  in
                       match uu____20154 with
                       | FStar_Syntax_Syntax.Tm_name uu____20159 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20161 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20186 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20186 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20188 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20191
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20192 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20195,uu____20196) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20238) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20244) ->
                           may_relate t
                       | uu____20249 -> false  in
                     let uu____20251 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20251 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20264 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20264
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20274 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20274
                          then
                            let uu____20277 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20277 with
                             | (guard,wl2) ->
                                 let uu____20284 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20284)
                          else
                            (let uu____20287 =
                               mklstr
                                 (fun uu____20298  ->
                                    let uu____20299 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20301 =
                                      let uu____20303 =
                                        let uu____20307 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20307
                                          (fun x  ->
                                             let uu____20314 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20314)
                                         in
                                      FStar_Util.dflt "" uu____20303  in
                                    let uu____20319 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20321 =
                                      let uu____20323 =
                                        let uu____20327 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20327
                                          (fun x  ->
                                             let uu____20334 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20334)
                                         in
                                      FStar_Util.dflt "" uu____20323  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20299 uu____20301 uu____20319
                                      uu____20321)
                                in
                             giveup env1 uu____20287 orig))
                 | (HeadMatch (true ),uu____20340) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20355 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20355 with
                        | (guard,wl2) ->
                            let uu____20362 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20362)
                     else
                       (let uu____20365 =
                          mklstr
                            (fun uu____20372  ->
                               let uu____20373 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20375 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20373 uu____20375)
                           in
                        giveup env1 uu____20365 orig)
                 | (uu____20378,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2862_20392 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2862_20392.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2862_20392.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2862_20392.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2862_20392.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2862_20392.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2862_20392.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2862_20392.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2862_20392.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20419 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20419
          then
            let uu____20422 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20422
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20428 =
                let uu____20431 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20431  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20428 t1);
             (let uu____20450 =
                let uu____20453 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20453  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20450 t2);
             (let uu____20472 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20472
              then
                let uu____20476 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20478 =
                  let uu____20480 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20482 =
                    let uu____20484 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20484  in
                  Prims.op_Hat uu____20480 uu____20482  in
                let uu____20487 =
                  let uu____20489 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20491 =
                    let uu____20493 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20493  in
                  Prims.op_Hat uu____20489 uu____20491  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20476 uu____20478 uu____20487
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20500,uu____20501) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20517,FStar_Syntax_Syntax.Tm_delayed uu____20518) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20534,uu____20535) ->
                  let uu____20562 =
                    let uu___2893_20563 = problem  in
                    let uu____20564 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2893_20563.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20564;
                      FStar_TypeChecker_Common.relation =
                        (uu___2893_20563.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2893_20563.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2893_20563.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2893_20563.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2893_20563.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2893_20563.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2893_20563.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2893_20563.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20562 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20565,uu____20566) ->
                  let uu____20573 =
                    let uu___2899_20574 = problem  in
                    let uu____20575 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2899_20574.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20575;
                      FStar_TypeChecker_Common.relation =
                        (uu___2899_20574.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2899_20574.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2899_20574.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2899_20574.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2899_20574.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2899_20574.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2899_20574.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2899_20574.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20573 wl
              | (uu____20576,FStar_Syntax_Syntax.Tm_ascribed uu____20577) ->
                  let uu____20604 =
                    let uu___2905_20605 = problem  in
                    let uu____20606 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2905_20605.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2905_20605.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2905_20605.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20606;
                      FStar_TypeChecker_Common.element =
                        (uu___2905_20605.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2905_20605.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2905_20605.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2905_20605.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2905_20605.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2905_20605.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20604 wl
              | (uu____20607,FStar_Syntax_Syntax.Tm_meta uu____20608) ->
                  let uu____20615 =
                    let uu___2911_20616 = problem  in
                    let uu____20617 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2911_20616.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2911_20616.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2911_20616.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20617;
                      FStar_TypeChecker_Common.element =
                        (uu___2911_20616.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2911_20616.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2911_20616.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2911_20616.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2911_20616.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2911_20616.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20615 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20619),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20621)) ->
                  let uu____20630 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20630
              | (FStar_Syntax_Syntax.Tm_bvar uu____20631,uu____20632) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20634,FStar_Syntax_Syntax.Tm_bvar uu____20635) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___26_20705 =
                    match uu___26_20705 with
                    | [] -> c
                    | bs ->
                        let uu____20733 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20733
                     in
                  let uu____20744 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20744 with
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
                                    let uu____20893 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20893
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
                  let mk_t t l uu___27_20982 =
                    match uu___27_20982 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21024 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21024 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21169 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21170 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21169
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21170 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21172,uu____21173) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21204 -> true
                    | uu____21224 -> false  in
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
                      (let uu____21284 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3013_21292 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3013_21292.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3013_21292.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3013_21292.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3013_21292.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3013_21292.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3013_21292.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3013_21292.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3013_21292.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3013_21292.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3013_21292.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3013_21292.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3013_21292.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3013_21292.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3013_21292.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3013_21292.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3013_21292.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3013_21292.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3013_21292.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3013_21292.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3013_21292.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3013_21292.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3013_21292.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3013_21292.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3013_21292.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3013_21292.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3013_21292.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3013_21292.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3013_21292.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3013_21292.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3013_21292.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3013_21292.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3013_21292.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3013_21292.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3013_21292.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3013_21292.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3013_21292.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3013_21292.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3013_21292.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3013_21292.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3013_21292.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3013_21292.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3013_21292.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3013_21292.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21284 with
                       | (uu____21297,ty,uu____21299) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21308 =
                                 let uu____21309 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21309.FStar_Syntax_Syntax.n  in
                               match uu____21308 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21312 ->
                                   let uu____21319 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21319
                               | uu____21320 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21323 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21323
                             then
                               let uu____21328 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21330 =
                                 let uu____21332 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21332
                                  in
                               let uu____21333 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21328 uu____21330 uu____21333
                             else ());
                            r1))
                     in
                  let uu____21338 =
                    let uu____21355 = maybe_eta t1  in
                    let uu____21362 = maybe_eta t2  in
                    (uu____21355, uu____21362)  in
                  (match uu____21338 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3034_21404 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3034_21404.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3034_21404.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3034_21404.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3034_21404.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3034_21404.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3034_21404.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3034_21404.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3034_21404.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21425 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21425
                       then
                         let uu____21428 = destruct_flex_t not_abs wl  in
                         (match uu____21428 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21445 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21445.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21445.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21445.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21445.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21445.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21445.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21445.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21445.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21448 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21448 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21471 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21471
                       then
                         let uu____21474 = destruct_flex_t not_abs wl  in
                         (match uu____21474 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21491 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21491.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21491.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21491.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21491.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21491.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21491.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21491.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21491.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21494 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21494 orig))
                   | uu____21497 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21515,FStar_Syntax_Syntax.Tm_abs uu____21516) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21547 -> true
                    | uu____21567 -> false  in
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
                      (let uu____21627 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3013_21635 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3013_21635.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3013_21635.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3013_21635.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3013_21635.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3013_21635.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3013_21635.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3013_21635.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3013_21635.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3013_21635.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3013_21635.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3013_21635.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3013_21635.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3013_21635.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3013_21635.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3013_21635.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3013_21635.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3013_21635.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3013_21635.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3013_21635.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3013_21635.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3013_21635.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3013_21635.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3013_21635.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3013_21635.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3013_21635.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3013_21635.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3013_21635.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3013_21635.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3013_21635.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3013_21635.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3013_21635.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3013_21635.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3013_21635.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3013_21635.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3013_21635.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3013_21635.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3013_21635.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3013_21635.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3013_21635.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3013_21635.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3013_21635.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3013_21635.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3013_21635.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21627 with
                       | (uu____21640,ty,uu____21642) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21651 =
                                 let uu____21652 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21652.FStar_Syntax_Syntax.n  in
                               match uu____21651 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21655 ->
                                   let uu____21662 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21662
                               | uu____21663 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21666 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21666
                             then
                               let uu____21671 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21673 =
                                 let uu____21675 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21675
                                  in
                               let uu____21676 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21671 uu____21673 uu____21676
                             else ());
                            r1))
                     in
                  let uu____21681 =
                    let uu____21698 = maybe_eta t1  in
                    let uu____21705 = maybe_eta t2  in
                    (uu____21698, uu____21705)  in
                  (match uu____21681 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3034_21747 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3034_21747.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3034_21747.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3034_21747.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3034_21747.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3034_21747.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3034_21747.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3034_21747.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3034_21747.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21768 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21768
                       then
                         let uu____21771 = destruct_flex_t not_abs wl  in
                         (match uu____21771 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21788 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21788.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21788.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21788.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21788.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21788.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21788.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21788.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21788.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21791 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21791 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21814 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21814
                       then
                         let uu____21817 = destruct_flex_t not_abs wl  in
                         (match uu____21817 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21834 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21834.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21834.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21834.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21834.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21834.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21834.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21834.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21834.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21837 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21837 orig))
                   | uu____21840 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21870 =
                    let uu____21875 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21875 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3074_21903 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3074_21903.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3074_21903.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3076_21905 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3076_21905.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3076_21905.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21906,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3074_21921 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3074_21921.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3074_21921.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3076_21923 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3076_21923.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3076_21923.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21924 -> (x1, x2)  in
                  (match uu____21870 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21943 = as_refinement false env t11  in
                       (match uu____21943 with
                        | (x12,phi11) ->
                            let uu____21951 = as_refinement false env t21  in
                            (match uu____21951 with
                             | (x22,phi21) ->
                                 ((let uu____21960 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21960
                                   then
                                     ((let uu____21965 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21967 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21969 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21965
                                         uu____21967 uu____21969);
                                      (let uu____21972 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21974 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21976 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21972
                                         uu____21974 uu____21976))
                                   else ());
                                  (let uu____21981 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21981 with
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
                                         let uu____22052 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22052
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22064 =
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
                                         (let uu____22077 =
                                            let uu____22080 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22080
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22077
                                            (p_guard base_prob));
                                         (let uu____22099 =
                                            let uu____22102 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22102
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22099
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22121 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22121)
                                          in
                                       let has_uvars =
                                         (let uu____22126 =
                                            let uu____22128 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22128
                                             in
                                          Prims.op_Negation uu____22126) ||
                                           (let uu____22132 =
                                              let uu____22134 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22134
                                               in
                                            Prims.op_Negation uu____22132)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22138 =
                                           let uu____22143 =
                                             let uu____22152 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22152]  in
                                           mk_t_problem wl1 uu____22143 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22138 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22175 =
                                                solve env1
                                                  (let uu___3119_22177 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3119_22177.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3119_22177.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3119_22177.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3119_22177.tcenv);
                                                     wl_implicits =
                                                       (uu___3119_22177.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22175 with
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
                                               | Success uu____22192 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22201 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22201
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3132_22210 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3132_22210.attempting);
                                                         wl_deferred =
                                                           (uu___3132_22210.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3132_22210.defer_ok);
                                                         smt_ok =
                                                           (uu___3132_22210.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3132_22210.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3132_22210.tcenv);
                                                         wl_implicits =
                                                           (uu___3132_22210.wl_implicits)
                                                       }  in
                                                     let uu____22212 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22212))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22215,FStar_Syntax_Syntax.Tm_uvar uu____22216) ->
                  let uu____22241 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22241 with
                   | (t11,wl1) ->
                       let uu____22248 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22248 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22257;
                    FStar_Syntax_Syntax.pos = uu____22258;
                    FStar_Syntax_Syntax.vars = uu____22259;_},uu____22260),FStar_Syntax_Syntax.Tm_uvar
                 uu____22261) ->
                  let uu____22310 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22310 with
                   | (t11,wl1) ->
                       let uu____22317 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22317 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22326,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22327;
                    FStar_Syntax_Syntax.pos = uu____22328;
                    FStar_Syntax_Syntax.vars = uu____22329;_},uu____22330))
                  ->
                  let uu____22379 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22379 with
                   | (t11,wl1) ->
                       let uu____22386 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22386 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22395;
                    FStar_Syntax_Syntax.pos = uu____22396;
                    FStar_Syntax_Syntax.vars = uu____22397;_},uu____22398),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22399;
                    FStar_Syntax_Syntax.pos = uu____22400;
                    FStar_Syntax_Syntax.vars = uu____22401;_},uu____22402))
                  ->
                  let uu____22475 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22475 with
                   | (t11,wl1) ->
                       let uu____22482 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22482 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22491,uu____22492) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22505 = destruct_flex_t t1 wl  in
                  (match uu____22505 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22512;
                    FStar_Syntax_Syntax.pos = uu____22513;
                    FStar_Syntax_Syntax.vars = uu____22514;_},uu____22515),uu____22516)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22553 = destruct_flex_t t1 wl  in
                  (match uu____22553 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22560,FStar_Syntax_Syntax.Tm_uvar uu____22561) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22574,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22575;
                    FStar_Syntax_Syntax.pos = uu____22576;
                    FStar_Syntax_Syntax.vars = uu____22577;_},uu____22578))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22615,FStar_Syntax_Syntax.Tm_arrow uu____22616) ->
                  solve_t' env
                    (let uu___3234_22644 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3234_22644.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3234_22644.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3234_22644.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3234_22644.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3234_22644.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3234_22644.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3234_22644.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3234_22644.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3234_22644.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22645;
                    FStar_Syntax_Syntax.pos = uu____22646;
                    FStar_Syntax_Syntax.vars = uu____22647;_},uu____22648),FStar_Syntax_Syntax.Tm_arrow
                 uu____22649) ->
                  solve_t' env
                    (let uu___3234_22701 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3234_22701.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3234_22701.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3234_22701.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3234_22701.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3234_22701.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3234_22701.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3234_22701.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3234_22701.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3234_22701.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22702,FStar_Syntax_Syntax.Tm_uvar uu____22703) ->
                  let uu____22716 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22716
              | (uu____22717,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22718;
                    FStar_Syntax_Syntax.pos = uu____22719;
                    FStar_Syntax_Syntax.vars = uu____22720;_},uu____22721))
                  ->
                  let uu____22758 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22758
              | (FStar_Syntax_Syntax.Tm_uvar uu____22759,uu____22760) ->
                  let uu____22773 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22773
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22774;
                    FStar_Syntax_Syntax.pos = uu____22775;
                    FStar_Syntax_Syntax.vars = uu____22776;_},uu____22777),uu____22778)
                  ->
                  let uu____22815 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22815
              | (FStar_Syntax_Syntax.Tm_refine uu____22816,uu____22817) ->
                  let t21 =
                    let uu____22825 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22825  in
                  solve_t env
                    (let uu___3269_22851 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3269_22851.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3269_22851.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3269_22851.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3269_22851.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3269_22851.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3269_22851.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3269_22851.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3269_22851.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3269_22851.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22852,FStar_Syntax_Syntax.Tm_refine uu____22853) ->
                  let t11 =
                    let uu____22861 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22861  in
                  solve_t env
                    (let uu___3276_22887 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3276_22887.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3276_22887.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3276_22887.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3276_22887.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3276_22887.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3276_22887.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3276_22887.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3276_22887.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3276_22887.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22969 =
                    let uu____22970 = guard_of_prob env wl problem t1 t2  in
                    match uu____22970 with
                    | (guard,wl1) ->
                        let uu____22977 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22977
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23196 = br1  in
                        (match uu____23196 with
                         | (p1,w1,uu____23225) ->
                             let uu____23242 = br2  in
                             (match uu____23242 with
                              | (p2,w2,uu____23265) ->
                                  let uu____23270 =
                                    let uu____23272 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23272  in
                                  if uu____23270
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23299 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23299 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23336 = br2  in
                                         (match uu____23336 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23369 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23369
                                                 in
                                              let uu____23374 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23405,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23426) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23485 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23485 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23374
                                                (fun uu____23557  ->
                                                   match uu____23557 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23594 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23594
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23615
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23615
                                                              then
                                                                let uu____23620
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23622
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23620
                                                                  uu____23622
                                                              else ());
                                                             (let uu____23628
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23628
                                                                (fun
                                                                   uu____23664
                                                                    ->
                                                                   match uu____23664
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
                    | uu____23793 -> FStar_Pervasives_Native.None  in
                  let uu____23834 = solve_branches wl brs1 brs2  in
                  (match uu____23834 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23860 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23860 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23887 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23887 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23921 =
                                FStar_List.map
                                  (fun uu____23933  ->
                                     match uu____23933 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23921  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23942 =
                              let uu____23943 =
                                let uu____23944 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23944
                                  (let uu___3375_23952 = wl3  in
                                   {
                                     attempting =
                                       (uu___3375_23952.attempting);
                                     wl_deferred =
                                       (uu___3375_23952.wl_deferred);
                                     ctr = (uu___3375_23952.ctr);
                                     defer_ok = (uu___3375_23952.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3375_23952.umax_heuristic_ok);
                                     tcenv = (uu___3375_23952.tcenv);
                                     wl_implicits =
                                       (uu___3375_23952.wl_implicits)
                                   })
                                 in
                              solve env uu____23943  in
                            (match uu____23942 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23957 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23966 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23966 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23969,uu____23970) ->
                  let head1 =
                    let uu____23994 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23994
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24040 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24040
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24086 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24086
                    then
                      let uu____24090 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24092 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24094 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24090 uu____24092 uu____24094
                    else ());
                   (let no_free_uvars t =
                      (let uu____24108 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24108) &&
                        (let uu____24112 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24112)
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
                      let uu____24131 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24131 = FStar_Syntax_Util.Equal  in
                    let uu____24132 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24132
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24136 = equal t1 t2  in
                         (if uu____24136
                          then
                            let uu____24139 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24139
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24144 =
                            let uu____24151 = equal t1 t2  in
                            if uu____24151
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24164 = mk_eq2 wl env orig t1 t2  in
                               match uu____24164 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24144 with
                          | (guard,wl1) ->
                              let uu____24185 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24185))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24188,uu____24189) ->
                  let head1 =
                    let uu____24197 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24197
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24243 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24243
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24289 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24289
                    then
                      let uu____24293 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24295 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24297 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24293 uu____24295 uu____24297
                    else ());
                   (let no_free_uvars t =
                      (let uu____24311 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24311) &&
                        (let uu____24315 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24315)
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
                      let uu____24334 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24334 = FStar_Syntax_Util.Equal  in
                    let uu____24335 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24335
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24339 = equal t1 t2  in
                         (if uu____24339
                          then
                            let uu____24342 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24342
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24347 =
                            let uu____24354 = equal t1 t2  in
                            if uu____24354
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24367 = mk_eq2 wl env orig t1 t2  in
                               match uu____24367 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24347 with
                          | (guard,wl1) ->
                              let uu____24388 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24388))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24391,uu____24392) ->
                  let head1 =
                    let uu____24394 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24394
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24440 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24440
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24486 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24486
                    then
                      let uu____24490 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24492 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24494 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24490 uu____24492 uu____24494
                    else ());
                   (let no_free_uvars t =
                      (let uu____24508 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24508) &&
                        (let uu____24512 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24512)
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
                      let uu____24531 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24531 = FStar_Syntax_Util.Equal  in
                    let uu____24532 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24532
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24536 = equal t1 t2  in
                         (if uu____24536
                          then
                            let uu____24539 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24539
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24544 =
                            let uu____24551 = equal t1 t2  in
                            if uu____24551
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24564 = mk_eq2 wl env orig t1 t2  in
                               match uu____24564 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24544 with
                          | (guard,wl1) ->
                              let uu____24585 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24585))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24588,uu____24589) ->
                  let head1 =
                    let uu____24591 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24591
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24637 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24637
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24683 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24683
                    then
                      let uu____24687 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24689 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24691 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24687 uu____24689 uu____24691
                    else ());
                   (let no_free_uvars t =
                      (let uu____24705 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24705) &&
                        (let uu____24709 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24709)
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
                      let uu____24728 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24728 = FStar_Syntax_Util.Equal  in
                    let uu____24729 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24729
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24733 = equal t1 t2  in
                         (if uu____24733
                          then
                            let uu____24736 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24736
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24741 =
                            let uu____24748 = equal t1 t2  in
                            if uu____24748
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24761 = mk_eq2 wl env orig t1 t2  in
                               match uu____24761 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24741 with
                          | (guard,wl1) ->
                              let uu____24782 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24782))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24785,uu____24786) ->
                  let head1 =
                    let uu____24788 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24788
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24834 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24834
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24880 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24880
                    then
                      let uu____24884 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24886 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24888 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24884 uu____24886 uu____24888
                    else ());
                   (let no_free_uvars t =
                      (let uu____24902 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24902) &&
                        (let uu____24906 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24906)
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
                      let uu____24925 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24925 = FStar_Syntax_Util.Equal  in
                    let uu____24926 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24926
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24930 = equal t1 t2  in
                         (if uu____24930
                          then
                            let uu____24933 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24933
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24938 =
                            let uu____24945 = equal t1 t2  in
                            if uu____24945
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24958 = mk_eq2 wl env orig t1 t2  in
                               match uu____24958 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24938 with
                          | (guard,wl1) ->
                              let uu____24979 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24979))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24982,uu____24983) ->
                  let head1 =
                    let uu____25001 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25001
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25047 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25047
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25093 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25093
                    then
                      let uu____25097 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25099 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25101 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25097 uu____25099 uu____25101
                    else ());
                   (let no_free_uvars t =
                      (let uu____25115 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25115) &&
                        (let uu____25119 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25119)
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
                      let uu____25138 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25138 = FStar_Syntax_Util.Equal  in
                    let uu____25139 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25139
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25143 = equal t1 t2  in
                         (if uu____25143
                          then
                            let uu____25146 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25146
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25151 =
                            let uu____25158 = equal t1 t2  in
                            if uu____25158
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25171 = mk_eq2 wl env orig t1 t2  in
                               match uu____25171 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25151 with
                          | (guard,wl1) ->
                              let uu____25192 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25192))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25195,FStar_Syntax_Syntax.Tm_match uu____25196) ->
                  let head1 =
                    let uu____25220 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25220
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25266 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25266
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25312 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25312
                    then
                      let uu____25316 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25318 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25320 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25316 uu____25318 uu____25320
                    else ());
                   (let no_free_uvars t =
                      (let uu____25334 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25334) &&
                        (let uu____25338 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25338)
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
                      let uu____25357 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25357 = FStar_Syntax_Util.Equal  in
                    let uu____25358 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25358
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25362 = equal t1 t2  in
                         (if uu____25362
                          then
                            let uu____25365 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25365
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25370 =
                            let uu____25377 = equal t1 t2  in
                            if uu____25377
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25390 = mk_eq2 wl env orig t1 t2  in
                               match uu____25390 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25370 with
                          | (guard,wl1) ->
                              let uu____25411 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25411))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25414,FStar_Syntax_Syntax.Tm_uinst uu____25415) ->
                  let head1 =
                    let uu____25423 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25423
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25469 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25469
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25515 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25515
                    then
                      let uu____25519 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25521 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25523 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25519 uu____25521 uu____25523
                    else ());
                   (let no_free_uvars t =
                      (let uu____25537 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25537) &&
                        (let uu____25541 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25541)
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
                      let uu____25560 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25560 = FStar_Syntax_Util.Equal  in
                    let uu____25561 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25561
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25565 = equal t1 t2  in
                         (if uu____25565
                          then
                            let uu____25568 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25568
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25573 =
                            let uu____25580 = equal t1 t2  in
                            if uu____25580
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25593 = mk_eq2 wl env orig t1 t2  in
                               match uu____25593 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25573 with
                          | (guard,wl1) ->
                              let uu____25614 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25614))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25617,FStar_Syntax_Syntax.Tm_name uu____25618) ->
                  let head1 =
                    let uu____25620 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25620
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25666 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25666
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25706 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25706
                    then
                      let uu____25710 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25712 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25714 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25710 uu____25712 uu____25714
                    else ());
                   (let no_free_uvars t =
                      (let uu____25728 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25728) &&
                        (let uu____25732 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25732)
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
                      let uu____25751 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25751 = FStar_Syntax_Util.Equal  in
                    let uu____25752 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25752
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25756 = equal t1 t2  in
                         (if uu____25756
                          then
                            let uu____25759 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25759
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25764 =
                            let uu____25771 = equal t1 t2  in
                            if uu____25771
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25784 = mk_eq2 wl env orig t1 t2  in
                               match uu____25784 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25764 with
                          | (guard,wl1) ->
                              let uu____25805 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25805))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25808,FStar_Syntax_Syntax.Tm_constant uu____25809) ->
                  let head1 =
                    let uu____25811 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25811
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25851 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25851
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25891 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25891
                    then
                      let uu____25895 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25897 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25899 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25895 uu____25897 uu____25899
                    else ());
                   (let no_free_uvars t =
                      (let uu____25913 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25913) &&
                        (let uu____25917 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25917)
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
                      let uu____25936 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25936 = FStar_Syntax_Util.Equal  in
                    let uu____25937 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25937
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25941 = equal t1 t2  in
                         (if uu____25941
                          then
                            let uu____25944 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25944
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25949 =
                            let uu____25956 = equal t1 t2  in
                            if uu____25956
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25969 = mk_eq2 wl env orig t1 t2  in
                               match uu____25969 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25949 with
                          | (guard,wl1) ->
                              let uu____25990 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25990))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25993,FStar_Syntax_Syntax.Tm_fvar uu____25994) ->
                  let head1 =
                    let uu____25996 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25996
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26042 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26042
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26088 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26088
                    then
                      let uu____26092 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26094 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26096 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26092 uu____26094 uu____26096
                    else ());
                   (let no_free_uvars t =
                      (let uu____26110 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26110) &&
                        (let uu____26114 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26114)
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
                      let uu____26133 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26133 = FStar_Syntax_Util.Equal  in
                    let uu____26134 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26134
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26138 = equal t1 t2  in
                         (if uu____26138
                          then
                            let uu____26141 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26141
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26146 =
                            let uu____26153 = equal t1 t2  in
                            if uu____26153
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26166 = mk_eq2 wl env orig t1 t2  in
                               match uu____26166 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26146 with
                          | (guard,wl1) ->
                              let uu____26187 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26187))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26190,FStar_Syntax_Syntax.Tm_app uu____26191) ->
                  let head1 =
                    let uu____26209 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26209
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26249 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26249
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26289 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26289
                    then
                      let uu____26293 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26295 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26297 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26293 uu____26295 uu____26297
                    else ());
                   (let no_free_uvars t =
                      (let uu____26311 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26311) &&
                        (let uu____26315 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26315)
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
                      let uu____26334 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26334 = FStar_Syntax_Util.Equal  in
                    let uu____26335 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26335
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26339 = equal t1 t2  in
                         (if uu____26339
                          then
                            let uu____26342 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26342
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26347 =
                            let uu____26354 = equal t1 t2  in
                            if uu____26354
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26367 = mk_eq2 wl env orig t1 t2  in
                               match uu____26367 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26347 with
                          | (guard,wl1) ->
                              let uu____26388 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26388))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26391,FStar_Syntax_Syntax.Tm_let uu____26392) ->
                  let uu____26419 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26419
                  then
                    let uu____26422 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26422
                  else
                    (let uu____26425 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26425 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26428,uu____26429) ->
                  let uu____26443 =
                    let uu____26449 =
                      let uu____26451 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26453 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26455 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26457 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26451 uu____26453 uu____26455 uu____26457
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26449)
                     in
                  FStar_Errors.raise_error uu____26443
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26461,FStar_Syntax_Syntax.Tm_let uu____26462) ->
                  let uu____26476 =
                    let uu____26482 =
                      let uu____26484 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26486 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26488 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26490 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26484 uu____26486 uu____26488 uu____26490
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26482)
                     in
                  FStar_Errors.raise_error uu____26476
                    t1.FStar_Syntax_Syntax.pos
              | uu____26494 ->
                  let uu____26499 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26499 orig))))

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
          (let uu____26565 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26565
           then
             let uu____26570 =
               let uu____26572 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26572  in
             let uu____26573 =
               let uu____26575 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26575  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26570 uu____26573
           else ());
          (let uu____26579 =
             let uu____26581 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26581  in
           if uu____26579
           then
             let uu____26584 =
               mklstr
                 (fun uu____26591  ->
                    let uu____26592 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26594 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26592 uu____26594)
                in
             giveup env uu____26584 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26616 =
                  mklstr
                    (fun uu____26623  ->
                       let uu____26624 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26626 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26624 uu____26626)
                   in
                giveup env uu____26616 orig)
             else
               (let uu____26631 =
                  FStar_List.fold_left2
                    (fun uu____26652  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26652 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26673 =
                                 let uu____26678 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26679 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26678
                                   FStar_TypeChecker_Common.EQ uu____26679
                                   "effect universes"
                                  in
                               (match uu____26673 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26631 with
                | (univ_sub_probs,wl1) ->
                    let uu____26699 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26699 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26707 =
                           FStar_List.fold_right2
                             (fun uu____26744  ->
                                fun uu____26745  ->
                                  fun uu____26746  ->
                                    match (uu____26744, uu____26745,
                                            uu____26746)
                                    with
                                    | ((a1,uu____26790),(a2,uu____26792),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26825 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26825 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26707 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26852 =
                                  let uu____26855 =
                                    let uu____26858 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26858
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26855
                                   in
                                FStar_List.append univ_sub_probs uu____26852
                                 in
                              let guard =
                                let guard =
                                  let uu____26880 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26880  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3527_26889 = wl3  in
                                {
                                  attempting = (uu___3527_26889.attempting);
                                  wl_deferred = (uu___3527_26889.wl_deferred);
                                  ctr = (uu___3527_26889.ctr);
                                  defer_ok = (uu___3527_26889.defer_ok);
                                  smt_ok = (uu___3527_26889.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3527_26889.umax_heuristic_ok);
                                  tcenv = (uu___3527_26889.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26891 = attempt sub_probs wl5  in
                              solve env uu____26891))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26909 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26909
           then
             let uu____26914 =
               let uu____26916 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26916
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26918 =
               let uu____26920 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26920
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26914 uu____26918
           else ());
          (let uu____26925 =
             let uu____26930 =
               let uu____26935 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26935
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26930
               (fun uu____26952  ->
                  match uu____26952 with
                  | (c,g) ->
                      let uu____26963 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26963, g))
              in
           match uu____26925 with
           | (c12,g_lift) ->
               ((let uu____26967 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26967
                 then
                   let uu____26972 =
                     let uu____26974 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26974
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26976 =
                     let uu____26978 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26978
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26972 uu____26976
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3547_26988 = wl  in
                     {
                       attempting = (uu___3547_26988.attempting);
                       wl_deferred = (uu___3547_26988.wl_deferred);
                       ctr = (uu___3547_26988.ctr);
                       defer_ok = (uu___3547_26988.defer_ok);
                       smt_ok = (uu___3547_26988.smt_ok);
                       umax_heuristic_ok =
                         (uu___3547_26988.umax_heuristic_ok);
                       tcenv = (uu___3547_26988.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26989 =
                     let rec is_uvar t =
                       let uu____27003 =
                         let uu____27004 = FStar_Syntax_Subst.compress t  in
                         uu____27004.FStar_Syntax_Syntax.n  in
                       match uu____27003 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27008 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27023) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27029) ->
                           is_uvar t1
                       | uu____27054 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27088  ->
                          fun uu____27089  ->
                            fun uu____27090  ->
                              match (uu____27088, uu____27089, uu____27090)
                              with
                              | ((a1,uu____27134),(a2,uu____27136),(is_sub_probs,wl2))
                                  ->
                                  let uu____27169 = is_uvar a1  in
                                  if uu____27169
                                  then
                                    ((let uu____27179 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27179
                                      then
                                        let uu____27184 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27186 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27184 uu____27186
                                      else ());
                                     (let uu____27191 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27191 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26989 with
                   | (is_sub_probs,wl2) ->
                       let uu____27219 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27219 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27227 =
                              let uu____27232 =
                                let uu____27233 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27233
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27232
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27227 with
                             | (uu____27240,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27251 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27253 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27251 s uu____27253
                                    in
                                 let uu____27256 =
                                   let uu____27285 =
                                     let uu____27286 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27286.FStar_Syntax_Syntax.n  in
                                   match uu____27285 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27346 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27346 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27409 =
                                              let uu____27428 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27428
                                                (fun uu____27532  ->
                                                   match uu____27532 with
                                                   | (l1,l2) ->
                                                       let uu____27605 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27605))
                                               in
                                            (match uu____27409 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27710 ->
                                       let uu____27711 =
                                         let uu____27717 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27717)
                                          in
                                       FStar_Errors.raise_error uu____27711 r
                                    in
                                 (match uu____27256 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27793 =
                                        let uu____27800 =
                                          let uu____27801 =
                                            let uu____27802 =
                                              let uu____27809 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27809,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27802
                                             in
                                          [uu____27801]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27800
                                          (fun b  ->
                                             let uu____27825 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27827 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27829 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27825 uu____27827
                                               uu____27829) r
                                         in
                                      (match uu____27793 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27839 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27839
                                             then
                                               let uu____27844 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27853 =
                                                          let uu____27855 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27855
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27853) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27844
                                             else ());
                                            (let wl4 =
                                               let uu___3619_27863 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3619_27863.attempting);
                                                 wl_deferred =
                                                   (uu___3619_27863.wl_deferred);
                                                 ctr = (uu___3619_27863.ctr);
                                                 defer_ok =
                                                   (uu___3619_27863.defer_ok);
                                                 smt_ok =
                                                   (uu___3619_27863.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3619_27863.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3619_27863.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27888 =
                                                        let uu____27895 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27895, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27888) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27912 =
                                               let f_sort_is =
                                                 let uu____27922 =
                                                   let uu____27923 =
                                                     let uu____27926 =
                                                       let uu____27927 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27927.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27926
                                                      in
                                                   uu____27923.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27922 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27938,uu____27939::is)
                                                     ->
                                                     let uu____27981 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27981
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28014 ->
                                                     let uu____28015 =
                                                       let uu____28021 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28021)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28015 r
                                                  in
                                               let uu____28027 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28062  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28062
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28083 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28083
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28027
                                                in
                                             match uu____27912 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28108 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28108
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28109 =
                                                   let g_sort_is =
                                                     let uu____28119 =
                                                       let uu____28120 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28120.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28119 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28125,uu____28126::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28186 ->
                                                         let uu____28187 =
                                                           let uu____28193 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28193)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28187 r
                                                      in
                                                   let uu____28199 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28234  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28234
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28255
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28255
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28199
                                                    in
                                                 (match uu____28109 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28282 =
                                                          let uu____28287 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28288 =
                                                            let uu____28289 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28289
                                                             in
                                                          (uu____28287,
                                                            uu____28288)
                                                           in
                                                        match uu____28282
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28317 =
                                                          let uu____28320 =
                                                            let uu____28323 =
                                                              let uu____28326
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28326
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28323
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28320
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28317
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28350 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28350
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
                                                        let uu____28361 =
                                                          let uu____28364 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28367 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28367)
                                                            uu____28364
                                                           in
                                                        solve_prob orig
                                                          uu____28361 [] wl6
                                                         in
                                                      let uu____28368 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28368))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28391 =
            let univs =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28393 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28393]
              | x -> x  in
            let c12 =
              let uu___3685_28396 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3685_28396.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3685_28396.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3685_28396.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3685_28396.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28397 =
              let uu____28402 =
                FStar_All.pipe_right
                  (let uu___3688_28404 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3688_28404.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3688_28404.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3688_28404.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3688_28404.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28402
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28397
              (fun uu____28418  ->
                 match uu____28418 with
                 | (c,g) ->
                     let uu____28425 =
                       let uu____28427 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28427  in
                     if uu____28425
                     then
                       let uu____28430 =
                         let uu____28436 =
                           let uu____28438 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28440 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28438 uu____28440
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28436)
                          in
                       FStar_Errors.raise_error uu____28430 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28446 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28446
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28452 = lift_c1 ()  in
               solve_eq uu____28452 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___28_28461  ->
                         match uu___28_28461 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28466 -> false))
                  in
               let uu____28468 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28498)::uu____28499,(wp2,uu____28501)::uu____28502)
                     -> (wp1, wp2)
                 | uu____28575 ->
                     let uu____28600 =
                       let uu____28606 =
                         let uu____28608 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28610 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28608 uu____28610
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28606)
                        in
                     FStar_Errors.raise_error uu____28600
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28468 with
               | (wpc1,wpc2) ->
                   let uu____28620 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28620
                   then
                     let uu____28623 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28623 wl
                   else
                     (let uu____28627 =
                        let uu____28634 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28634  in
                      match uu____28627 with
                      | (c2_decl,qualifiers) ->
                          let uu____28655 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28655
                          then
                            let c1_repr =
                              let uu____28662 =
                                let uu____28663 =
                                  let uu____28664 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28664  in
                                let uu____28665 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28663 uu____28665
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28662
                               in
                            let c2_repr =
                              let uu____28668 =
                                let uu____28669 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28670 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28669 uu____28670
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28668
                               in
                            let uu____28672 =
                              let uu____28677 =
                                let uu____28679 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28681 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28679
                                  uu____28681
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28677
                               in
                            (match uu____28672 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28687 = attempt [prob] wl2  in
                                 solve env uu____28687)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28707 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28707
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28730 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28730
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
                                        let uu____28740 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28740 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28747 =
                                        let uu____28754 =
                                          let uu____28755 =
                                            let uu____28772 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28775 =
                                              let uu____28786 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28786; wpc1_2]  in
                                            (uu____28772, uu____28775)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28755
                                           in
                                        FStar_Syntax_Syntax.mk uu____28754
                                         in
                                      uu____28747
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
                                     let uu____28835 =
                                       let uu____28842 =
                                         let uu____28843 =
                                           let uu____28860 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28863 =
                                             let uu____28874 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28883 =
                                               let uu____28894 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28894; wpc1_2]  in
                                             uu____28874 :: uu____28883  in
                                           (uu____28860, uu____28863)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28843
                                          in
                                       FStar_Syntax_Syntax.mk uu____28842  in
                                     uu____28835 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28948 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28948
                              then
                                let uu____28953 =
                                  let uu____28955 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28955
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28953
                              else ());
                             (let uu____28959 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28959 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28968 =
                                      let uu____28971 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____28974  ->
                                           FStar_Pervasives_Native.Some
                                             uu____28974) uu____28971
                                       in
                                    solve_prob orig uu____28968 [] wl1  in
                                  let uu____28975 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28975))))
           in
        let uu____28976 = FStar_Util.physical_equality c1 c2  in
        if uu____28976
        then
          let uu____28979 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28979
        else
          ((let uu____28983 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28983
            then
              let uu____28988 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28990 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28988
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28990
            else ());
           (let uu____28995 =
              let uu____29004 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29007 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29004, uu____29007)  in
            match uu____28995 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29025),FStar_Syntax_Syntax.Total
                    (t2,uu____29027)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29044 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29044 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29046,FStar_Syntax_Syntax.Total uu____29047) ->
                     let uu____29064 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29064 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29068),FStar_Syntax_Syntax.Total
                    (t2,uu____29070)) ->
                     let uu____29087 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29087 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29090),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29092)) ->
                     let uu____29109 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29109 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29112),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29114)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29131 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29131 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29134),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29136)) ->
                     let uu____29153 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29153 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29156,FStar_Syntax_Syntax.Comp uu____29157) ->
                     let uu____29166 =
                       let uu___3812_29169 = problem  in
                       let uu____29172 =
                         let uu____29173 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29173
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3812_29169.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29172;
                         FStar_TypeChecker_Common.relation =
                           (uu___3812_29169.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3812_29169.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3812_29169.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3812_29169.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3812_29169.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3812_29169.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3812_29169.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3812_29169.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29166 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29174,FStar_Syntax_Syntax.Comp uu____29175) ->
                     let uu____29184 =
                       let uu___3812_29187 = problem  in
                       let uu____29190 =
                         let uu____29191 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29191
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3812_29187.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29190;
                         FStar_TypeChecker_Common.relation =
                           (uu___3812_29187.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3812_29187.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3812_29187.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3812_29187.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3812_29187.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3812_29187.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3812_29187.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3812_29187.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29184 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29192,FStar_Syntax_Syntax.GTotal uu____29193) ->
                     let uu____29202 =
                       let uu___3824_29205 = problem  in
                       let uu____29208 =
                         let uu____29209 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29209
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3824_29205.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3824_29205.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3824_29205.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29208;
                         FStar_TypeChecker_Common.element =
                           (uu___3824_29205.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3824_29205.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3824_29205.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3824_29205.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3824_29205.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3824_29205.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29202 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29210,FStar_Syntax_Syntax.Total uu____29211) ->
                     let uu____29220 =
                       let uu___3824_29223 = problem  in
                       let uu____29226 =
                         let uu____29227 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29227
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3824_29223.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3824_29223.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3824_29223.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29226;
                         FStar_TypeChecker_Common.element =
                           (uu___3824_29223.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3824_29223.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3824_29223.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3824_29223.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3824_29223.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3824_29223.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29220 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29228,FStar_Syntax_Syntax.Comp uu____29229) ->
                     let uu____29230 =
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
                     if uu____29230
                     then
                       let uu____29233 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29233 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29240 =
                            let uu____29245 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29245
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29254 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29255 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29254, uu____29255))
                             in
                          match uu____29240 with
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
                           (let uu____29263 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29263
                            then
                              let uu____29268 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29270 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29268 uu____29270
                            else ());
                           (let uu____29275 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29275 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29278 =
                                  mklstr
                                    (fun uu____29285  ->
                                       let uu____29286 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29288 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29286 uu____29288)
                                   in
                                giveup env uu____29278 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29299 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29299 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29349 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29349 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29374 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29405  ->
                match uu____29405 with
                | (u1,u2) ->
                    let uu____29413 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29415 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29413 uu____29415))
         in
      FStar_All.pipe_right uu____29374 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29452,[])) when
          let uu____29479 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29479 -> "{}"
      | uu____29482 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29509 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29509
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29521 =
              FStar_List.map
                (fun uu____29534  ->
                   match uu____29534 with
                   | (uu____29541,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29521 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29552 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29552 imps
  
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
                  let uu____29609 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29609
                  then
                    let uu____29617 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29619 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29617
                      (rel_to_string rel) uu____29619
                  else "TOP"  in
                let uu____29625 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29625 with
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
              let uu____29685 =
                let uu____29688 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____29691  ->
                     FStar_Pervasives_Native.Some uu____29691) uu____29688
                 in
              FStar_Syntax_Syntax.new_bv uu____29685 t1  in
            let uu____29692 =
              let uu____29697 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29697
               in
            match uu____29692 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29755 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29755
         then
           let uu____29760 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29760
         else ());
        (let uu____29767 =
           FStar_Util.record_time (fun uu____29774  -> solve env probs)  in
         match uu____29767 with
         | (sol,ms) ->
             ((let uu____29786 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29786
               then
                 let uu____29791 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29791
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29804 =
                     FStar_Util.record_time
                       (fun uu____29811  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29804 with
                    | ((),ms1) ->
                        ((let uu____29822 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29822
                          then
                            let uu____29827 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29827
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29839 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29839
                     then
                       let uu____29846 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29846
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
          ((let uu____29872 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29872
            then
              let uu____29877 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29877
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29885 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29885
             then
               let uu____29890 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29890
             else ());
            (let f2 =
               let uu____29896 =
                 let uu____29897 = FStar_Syntax_Util.unmeta f1  in
                 uu____29897.FStar_Syntax_Syntax.n  in
               match uu____29896 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29901 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3941_29902 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3941_29902.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3941_29902.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3941_29902.FStar_TypeChecker_Common.implicits)
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
            let uu____29945 =
              let uu____29946 =
                let uu____29947 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____29948  ->
                       FStar_TypeChecker_Common.NonTrivial uu____29948)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29947;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29946  in
            FStar_All.pipe_left
              (fun uu____29955  -> FStar_Pervasives_Native.Some uu____29955)
              uu____29945
  
let with_guard_no_simp :
  'uuuuuu29965 .
    'uuuuuu29965 ->
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
            let uu____30005 =
              let uu____30006 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30007  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30007)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30006;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30005
  
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
          (let uu____30040 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30040
           then
             let uu____30045 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30047 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30045
               uu____30047
           else ());
          (let uu____30052 =
             let uu____30057 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30057
              in
           match uu____30052 with
           | (prob,wl) ->
               let g =
                 let uu____30065 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30073  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30065  in
               ((let uu____30091 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30091
                 then
                   let uu____30096 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30096
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
        let uu____30117 = try_teq true env t1 t2  in
        match uu____30117 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30122 = FStar_TypeChecker_Env.get_range env  in
              let uu____30123 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30122 uu____30123);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30131 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30131
              then
                let uu____30136 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30138 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30140 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30136
                  uu____30138 uu____30140
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
        (let uu____30164 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30164
         then
           let uu____30169 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30171 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30169
             uu____30171
         else ());
        (let uu____30176 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30176 with
         | (prob,x,wl) ->
             let g =
               let uu____30191 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30200  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30191  in
             ((let uu____30218 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30218
               then
                 let uu____30223 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30223
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30231 =
                     let uu____30232 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30232 g1  in
                   FStar_Pervasives_Native.Some uu____30231)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30254 = FStar_TypeChecker_Env.get_range env  in
          let uu____30255 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30254 uu____30255
  
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
        (let uu____30284 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30284
         then
           let uu____30289 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30291 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30289 uu____30291
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30302 =
           let uu____30309 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30309 "sub_comp"
            in
         match uu____30302 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30322 =
                 FStar_Util.record_time
                   (fun uu____30334  ->
                      let uu____30335 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30344  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30335)
                  in
               match uu____30322 with
               | (r,ms) ->
                   ((let uu____30372 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30372
                     then
                       let uu____30377 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30379 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30381 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30377 uu____30379
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30381
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
      fun uu____30419  ->
        match uu____30419 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30462 =
                 let uu____30468 =
                   let uu____30470 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30472 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30470 uu____30472
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30468)  in
               let uu____30476 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30462 uu____30476)
               in
            let equiv v v' =
              let uu____30489 =
                let uu____30494 = FStar_Syntax_Subst.compress_univ v  in
                let uu____30495 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30494, uu____30495)  in
              match uu____30489 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30515 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____30546 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____30546 with
                      | FStar_Syntax_Syntax.U_unif uu____30553 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30582  ->
                                    match uu____30582 with
                                    | (u,v') ->
                                        let uu____30591 = equiv v v'  in
                                        if uu____30591
                                        then
                                          let uu____30596 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____30596 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____30617 -> []))
               in
            let uu____30622 =
              let wl =
                let uu___4052_30626 = empty_worklist env  in
                {
                  attempting = (uu___4052_30626.attempting);
                  wl_deferred = (uu___4052_30626.wl_deferred);
                  ctr = (uu___4052_30626.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4052_30626.smt_ok);
                  umax_heuristic_ok = (uu___4052_30626.umax_heuristic_ok);
                  tcenv = (uu___4052_30626.tcenv);
                  wl_implicits = (uu___4052_30626.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30645  ->
                      match uu____30645 with
                      | (lb,v) ->
                          let uu____30652 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____30652 with
                           | USolved wl1 -> ()
                           | uu____30655 -> fail lb v)))
               in
            let rec check_ineq uu____30666 =
              match uu____30666 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30678) -> true
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
                      uu____30702,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30704,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30715) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____30723,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____30732 -> false)
               in
            let uu____30738 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30755  ->
                      match uu____30755 with
                      | (u,v) ->
                          let uu____30763 = check_ineq (u, v)  in
                          if uu____30763
                          then true
                          else
                            ((let uu____30771 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30771
                              then
                                let uu____30776 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30778 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____30776
                                  uu____30778
                              else ());
                             false)))
               in
            if uu____30738
            then ()
            else
              ((let uu____30788 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30788
                then
                  ((let uu____30794 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30794);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30806 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30806))
                else ());
               (let uu____30819 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30819))
  
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
        let fail uu____30892 =
          match uu____30892 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4129_30915 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4129_30915.attempting);
            wl_deferred = (uu___4129_30915.wl_deferred);
            ctr = (uu___4129_30915.ctr);
            defer_ok;
            smt_ok = (uu___4129_30915.smt_ok);
            umax_heuristic_ok = (uu___4129_30915.umax_heuristic_ok);
            tcenv = (uu___4129_30915.tcenv);
            wl_implicits = (uu___4129_30915.wl_implicits)
          }  in
        (let uu____30918 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30918
         then
           let uu____30923 = FStar_Util.string_of_bool defer_ok  in
           let uu____30925 = wl_to_string wl  in
           let uu____30927 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30923 uu____30925 uu____30927
         else ());
        (let g1 =
           let uu____30933 = solve_and_commit env wl fail  in
           match uu____30933 with
           | FStar_Pervasives_Native.Some
               (uu____30940::uu____30941,uu____30942) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4144_30971 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4144_30971.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4144_30971.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30972 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4149_30981 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4149_30981.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4149_30981.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4149_30981.FStar_TypeChecker_Common.implicits)
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
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___4161_31058 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4161_31058.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4161_31058.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4161_31058.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31059 =
            let uu____31061 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31061  in
          if uu____31059
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug
                  then
                    (let uu____31073 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31074 =
                       let uu____31076 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31076
                        in
                     FStar_Errors.diag uu____31073 uu____31074)
                  else ();
                  (let vc1 =
                     let uu____31082 =
                       let uu____31086 =
                         let uu____31088 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31088  in
                       FStar_Pervasives_Native.Some uu____31086  in
                     FStar_Profiling.profile
                       (fun uu____31091  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31082 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug
                   then
                     (let uu____31095 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31096 =
                        let uu____31098 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31098
                         in
                      FStar_Errors.diag uu____31095 uu____31096)
                   else ();
                   (let uu____31104 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31104
                      "discharge_guard'" env vc1);
                   (let uu____31106 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31106 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug
                           then
                             (let uu____31115 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31116 =
                                let uu____31118 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31118
                                 in
                              FStar_Errors.diag uu____31115 uu____31116)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug
                           then
                             (let uu____31128 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31129 =
                                let uu____31131 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31131
                                 in
                              FStar_Errors.diag uu____31128 uu____31129)
                           else ();
                           (let vcs =
                              let uu____31145 = FStar_Options.use_tactics ()
                                 in
                              if uu____31145
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31167  ->
                                     (let uu____31169 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____31171  -> ()) uu____31169);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31214  ->
                                              match uu____31214 with
                                              | (env1,goal,opts) ->
                                                  let uu____31230 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31230, opts)))))
                              else
                                (let uu____31234 =
                                   let uu____31241 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31241)  in
                                 [uu____31234])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31274  ->
                                    match uu____31274 with
                                    | (env1,goal,opts) ->
                                        let uu____31284 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31284 with
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
                                                (let uu____31295 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31296 =
                                                   let uu____31298 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31300 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31298 uu____31300
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31295 uu____31296)
                                              else ();
                                              if debug
                                              then
                                                (let uu____31307 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31308 =
                                                   let uu____31310 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31310
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31307 uu____31308)
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
      let uu____31328 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31328 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31337 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31337
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31351 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31351 with
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
        let uu____31381 = try_teq false env t1 t2  in
        match uu____31381 with
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
            let uu____31425 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31425 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31438 ->
                     let uu____31451 =
                       let uu____31452 = FStar_Syntax_Subst.compress r  in
                       uu____31452.FStar_Syntax_Syntax.n  in
                     (match uu____31451 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31457) ->
                          unresolved ctx_u'
                      | uu____31474 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31498 = acc  in
            match uu____31498 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____31517 = hd  in
                     (match uu____31517 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____31528 = unresolved ctx_u  in
                             if uu____31528
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd :: out), changed) tl
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31552 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31552
                                     then
                                       let uu____31556 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31556
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31565 = teq_nosmt env1 t tm
                                          in
                                       match uu____31565 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4274_31575 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4274_31575.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4274_31575.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4274_31575.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4274_31575.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4274_31575.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4274_31575.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4274_31575.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4277_31583 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4277_31583.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4277_31583.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4277_31583.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4281_31594 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4281_31594.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4281_31594.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4281_31594.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4281_31594.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4281_31594.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4281_31594.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4281_31594.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4281_31594.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4281_31594.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4281_31594.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4281_31594.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4281_31594.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4281_31594.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4281_31594.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4281_31594.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4281_31594.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4281_31594.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4281_31594.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4281_31594.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4281_31594.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4281_31594.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4281_31594.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4281_31594.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4281_31594.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4281_31594.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4281_31594.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4281_31594.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4281_31594.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4281_31594.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4281_31594.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4281_31594.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4281_31594.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4281_31594.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4281_31594.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4281_31594.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4281_31594.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4281_31594.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4281_31594.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4281_31594.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4281_31594.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4281_31594.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4281_31594.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4281_31594.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4281_31594.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4281_31594.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4286_31599 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4286_31599.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4286_31599.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4286_31599.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4286_31599.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4286_31599.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4286_31599.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4286_31599.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4286_31599.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4286_31599.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4286_31599.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4286_31599.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4286_31599.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4286_31599.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4286_31599.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4286_31599.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4286_31599.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4286_31599.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4286_31599.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4286_31599.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4286_31599.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4286_31599.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4286_31599.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4286_31599.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4286_31599.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4286_31599.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4286_31599.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4286_31599.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4286_31599.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4286_31599.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4286_31599.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4286_31599.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4286_31599.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4286_31599.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4286_31599.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4286_31599.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4286_31599.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4286_31599.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31604 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31604
                                   then
                                     let uu____31609 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31611 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31613 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31615 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31609 uu____31611 uu____31613
                                       reason uu____31615
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4292_31622  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31629 =
                                             let uu____31639 =
                                               let uu____31647 =
                                                 let uu____31649 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31651 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31653 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31649 uu____31651
                                                   uu____31653
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31647, r)
                                                in
                                             [uu____31639]  in
                                           FStar_Errors.add_errors
                                             uu____31629);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31672 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31683  ->
                                               let uu____31684 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31686 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31688 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31684 uu____31686
                                                 reason uu____31688)) env2 g1
                                         true
                                        in
                                     match uu____31672 with
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
          let uu___4304_31696 = g  in
          let uu____31697 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4304_31696.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4304_31696.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4304_31696.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31697
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
        let uu____31737 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31737 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31738 = discharge_guard env g1  in
          FStar_All.pipe_left (fun uu____31739  -> ()) uu____31738
      | imp::uu____31741 ->
          let uu____31744 =
            let uu____31750 =
              let uu____31752 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31754 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31752 uu____31754
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31750)
             in
          FStar_Errors.raise_error uu____31744
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31774 = teq env t1 t2  in
        force_trivial_guard env uu____31774
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31793 = teq_nosmt env t1 t2  in
        match uu____31793 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4329_31812 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4329_31812.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4329_31812.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4329_31812.FStar_TypeChecker_Common.implicits)
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
        (let uu____31848 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31848
         then
           let uu____31853 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31855 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31853
             uu____31855
         else ());
        (let uu____31860 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31860 with
         | (prob,x,wl) ->
             let g =
               let uu____31879 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31888  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31879  in
             ((let uu____31906 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31906
               then
                 let uu____31911 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31913 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31915 =
                   let uu____31917 = FStar_Util.must g  in
                   guard_to_string env uu____31917  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31911 uu____31913 uu____31915
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
        let uu____31954 = check_subtyping env t1 t2  in
        match uu____31954 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31973 =
              let uu____31974 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31974 g  in
            FStar_Pervasives_Native.Some uu____31973
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31993 = check_subtyping env t1 t2  in
        match uu____31993 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32012 =
              let uu____32013 =
                let uu____32014 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32014]  in
              FStar_TypeChecker_Env.close_guard env uu____32013 g  in
            FStar_Pervasives_Native.Some uu____32012
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32052 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32052
         then
           let uu____32057 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32059 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32057
             uu____32059
         else ());
        (let uu____32064 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32064 with
         | (prob,x,wl) ->
             let g =
               let uu____32079 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32088  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32079  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32109 =
                      let uu____32110 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32110]  in
                    FStar_TypeChecker_Env.close_guard env uu____32109 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32151 = subtype_nosmt env t1 t2  in
        match uu____32151 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  