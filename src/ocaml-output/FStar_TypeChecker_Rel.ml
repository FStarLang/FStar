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
                                  FStar_Syntax_Util.eq_univs uv1 uv2))
                           in
                        if uu____9853 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____9877 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  -> FStar_Syntax_Util.eq_univs u u'))
                      in
                   Prims.op_Negation uu____9877)
               in
            let uu____9884 = filter u12  in
            let uu____9887 = filter u22  in (uu____9884, uu____9887)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9922 = filter_out_common_univs us1 us2  in
                   (match uu____9922 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9982 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9982 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9985 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10002  ->
                               let uu____10003 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10005 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10003 uu____10005))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10031 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10031 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10057 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10057 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10060 ->
                   ufailed_thunk
                     (fun uu____10071  ->
                        let uu____10072 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10074 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10072 uu____10074 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10077,uu____10078) ->
              let uu____10080 =
                let uu____10082 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10084 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10082 uu____10084
                 in
              failwith uu____10080
          | (FStar_Syntax_Syntax.U_unknown ,uu____10087) ->
              let uu____10088 =
                let uu____10090 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10092 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10090 uu____10092
                 in
              failwith uu____10088
          | (uu____10095,FStar_Syntax_Syntax.U_bvar uu____10096) ->
              let uu____10098 =
                let uu____10100 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10102 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10100 uu____10102
                 in
              failwith uu____10098
          | (uu____10105,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10106 =
                let uu____10108 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10110 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10108 uu____10110
                 in
              failwith uu____10106
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10115 =
                let uu____10117 = FStar_Ident.text_of_id x  in
                let uu____10119 = FStar_Ident.text_of_id y  in
                uu____10117 = uu____10119  in
              if uu____10115
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10146 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10146
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10163 = occurs_univ v1 u3  in
              if uu____10163
              then
                let uu____10166 =
                  let uu____10168 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10170 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10168 uu____10170
                   in
                try_umax_components u11 u21 uu____10166
              else
                (let uu____10175 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10175)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10187 = occurs_univ v1 u3  in
              if uu____10187
              then
                let uu____10190 =
                  let uu____10192 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10194 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10192 uu____10194
                   in
                try_umax_components u11 u21 uu____10190
              else
                (let uu____10199 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10199)
          | (FStar_Syntax_Syntax.U_max uu____10200,uu____10201) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10209 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10209
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10215,FStar_Syntax_Syntax.U_max uu____10216) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10224 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10224
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10230,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10232,FStar_Syntax_Syntax.U_name uu____10233) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10235) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10237) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10239,FStar_Syntax_Syntax.U_succ uu____10240) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10242,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10349 = bc1  in
      match uu____10349 with
      | (bs1,mk_cod1) ->
          let uu____10393 = bc2  in
          (match uu____10393 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10504 = aux xs ys  in
                     (match uu____10504 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10587 =
                       let uu____10594 = mk_cod1 xs  in ([], uu____10594)  in
                     let uu____10597 =
                       let uu____10604 = mk_cod2 ys  in ([], uu____10604)  in
                     (uu____10587, uu____10597)
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
                  let uu____10673 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10673 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10676 =
                    let uu____10677 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10677 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10676
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10682 = has_type_guard t1 t2  in (uu____10682, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10683 = has_type_guard t2 t1  in (uu____10683, wl)
  
let is_flex_pat :
  'uuuuuu10693 'uuuuuu10694 'uuuuuu10695 .
    ('uuuuuu10693 * 'uuuuuu10694 * 'uuuuuu10695 Prims.list) -> Prims.bool
  =
  fun uu___22_10709  ->
    match uu___22_10709 with
    | (uu____10718,uu____10719,[]) -> true
    | uu____10723 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10756 = f  in
      match uu____10756 with
      | (uu____10763,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10764;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10765;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10768;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10769;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10770;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10771;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10841  ->
                 match uu____10841 with
                 | (y,uu____10850) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11004 =
                  let uu____11019 =
                    let uu____11022 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11022  in
                  ((FStar_List.rev pat_binders), uu____11019)  in
                FStar_Pervasives_Native.Some uu____11004
            | (uu____11055,[]) ->
                let uu____11086 =
                  let uu____11101 =
                    let uu____11104 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11104  in
                  ((FStar_List.rev pat_binders), uu____11101)  in
                FStar_Pervasives_Native.Some uu____11086
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11195 =
                  let uu____11196 = FStar_Syntax_Subst.compress a  in
                  uu____11196.FStar_Syntax_Syntax.n  in
                (match uu____11195 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11216 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11216
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1631_11246 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1631_11246.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1631_11246.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11250 =
                            let uu____11251 =
                              let uu____11258 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11258)  in
                            FStar_Syntax_Syntax.NT uu____11251  in
                          [uu____11250]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1637_11274 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1637_11274.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1637_11274.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11275 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11315 =
                  let uu____11322 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11322  in
                (match uu____11315 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11381 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11406 ->
               let uu____11407 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11407 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11703 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11703
       then
         let uu____11708 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11708
       else ());
      (let uu____11714 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11714
       then
         let uu____11719 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11719
       else ());
      (let uu____11724 = next_prob probs  in
       match uu____11724 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1664_11751 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1664_11751.wl_deferred);
               ctr = (uu___1664_11751.ctr);
               defer_ok = (uu___1664_11751.defer_ok);
               smt_ok = (uu___1664_11751.smt_ok);
               umax_heuristic_ok = (uu___1664_11751.umax_heuristic_ok);
               tcenv = (uu___1664_11751.tcenv);
               wl_implicits = (uu___1664_11751.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11760 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11760
                 then
                   let uu____11763 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____11763
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
                       (let uu____11770 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd
                            probs1
                           in
                        solve env uu____11770)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1676_11776 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1676_11776.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1676_11776.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1676_11776.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1676_11776.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1676_11776.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1676_11776.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1676_11776.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1676_11776.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1676_11776.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11801 ->
                let uu____11811 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11876  ->
                          match uu____11876 with
                          | (c,uu____11886,uu____11887) -> c < probs.ctr))
                   in
                (match uu____11811 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11935 =
                            let uu____11940 =
                              FStar_List.map
                                (fun uu____11961  ->
                                   match uu____11961 with
                                   | (uu____11977,x,y) ->
                                       let uu____11988 = FStar_Thunk.force x
                                          in
                                       (uu____11988, y)) probs.wl_deferred
                               in
                            (uu____11940, (probs.wl_implicits))  in
                          Success uu____11935
                      | uu____11992 ->
                          let uu____12002 =
                            let uu___1694_12003 = probs  in
                            let uu____12004 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12025  ->
                                      match uu____12025 with
                                      | (uu____12033,uu____12034,y) -> y))
                               in
                            {
                              attempting = uu____12004;
                              wl_deferred = rest;
                              ctr = (uu___1694_12003.ctr);
                              defer_ok = (uu___1694_12003.defer_ok);
                              smt_ok = (uu___1694_12003.smt_ok);
                              umax_heuristic_ok =
                                (uu___1694_12003.umax_heuristic_ok);
                              tcenv = (uu___1694_12003.tcenv);
                              wl_implicits = (uu___1694_12003.wl_implicits)
                            }  in
                          solve env uu____12002))))

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
            let uu____12043 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12043 with
            | USolved wl1 ->
                let uu____12045 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12045
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12048 = defer_lit "" orig wl1  in
                solve env uu____12048

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
                  let uu____12099 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12099 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12102 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12115;
                  FStar_Syntax_Syntax.vars = uu____12116;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12119;
                  FStar_Syntax_Syntax.vars = uu____12120;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12133,uu____12134) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12142,FStar_Syntax_Syntax.Tm_uinst uu____12143) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12151 -> USolved wl

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
            ((let uu____12162 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12162
              then
                let uu____12167 = prob_to_string env orig  in
                let uu____12169 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12167 uu____12169
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
               let uu____12262 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12262 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12317 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12317
                then
                  let uu____12322 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12324 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12322 uu____12324
                else ());
               (let uu____12329 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12329 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12375 = eq_prob t1 t2 wl2  in
                         (match uu____12375 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12396 ->
                         let uu____12405 = eq_prob t1 t2 wl2  in
                         (match uu____12405 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12455 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12470 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12471 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12470, uu____12471)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12476 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12477 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12476, uu____12477)
                            in
                         (match uu____12455 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12508 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12508 with
                                | (t1_hd,t1_args) ->
                                    let uu____12553 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12553 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12619 =
                                              let uu____12626 =
                                                let uu____12637 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12637 :: t1_args  in
                                              let uu____12654 =
                                                let uu____12663 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12663 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12712  ->
                                                   fun uu____12713  ->
                                                     fun uu____12714  ->
                                                       match (uu____12712,
                                                               uu____12713,
                                                               uu____12714)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12764),
                                                          (a2,uu____12766))
                                                           ->
                                                           let uu____12803 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12803
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12626
                                                uu____12654
                                               in
                                            match uu____12619 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1848_12829 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1848_12829.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1848_12829.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1848_12829.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12840 =
                                                  solve env1 wl'  in
                                                (match uu____12840 with
                                                 | Success (uu____12843,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1857_12847
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1857_12847.attempting);
                                                            wl_deferred =
                                                              (uu___1857_12847.wl_deferred);
                                                            ctr =
                                                              (uu___1857_12847.ctr);
                                                            defer_ok =
                                                              (uu___1857_12847.defer_ok);
                                                            smt_ok =
                                                              (uu___1857_12847.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1857_12847.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1857_12847.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12848 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12880 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12880 with
                                | (t1_base,p1_opt) ->
                                    let uu____12916 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12916 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13015 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13015
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
                                               let uu____13068 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13068
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
                                               let uu____13100 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13100
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
                                               let uu____13132 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13132
                                           | uu____13135 -> t_base  in
                                         let uu____13152 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13152 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13166 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13166, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13173 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13173 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13209 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13209 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13245 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13245
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
                              let uu____13269 = combine t11 t21 wl2  in
                              (match uu____13269 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13302 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13302
                                     then
                                       let uu____13307 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13307
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13349 ts1 =
               match uu____13349 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13412 = pairwise out t wl2  in
                        (match uu____13412 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13448 =
               let uu____13459 = FStar_List.hd ts  in (uu____13459, [], wl1)
                in
             let uu____13468 = FStar_List.tl ts  in
             aux uu____13448 uu____13468  in
           let uu____13475 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13475 with
           | (this_flex,this_rigid) ->
               let uu____13501 =
                 let uu____13502 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13502.FStar_Syntax_Syntax.n  in
               (match uu____13501 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13527 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13527
                    then
                      let uu____13530 = destruct_flex_t this_flex wl  in
                      (match uu____13530 with
                       | (flex,wl1) ->
                           let uu____13537 = quasi_pattern env flex  in
                           (match uu____13537 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____13556 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13556
                                  then
                                    let uu____13561 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13561
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13568 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1959_13571 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1959_13571.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1959_13571.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1959_13571.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1959_13571.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1959_13571.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1959_13571.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1959_13571.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1959_13571.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1959_13571.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13568)
                | uu____13572 ->
                    ((let uu____13574 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13574
                      then
                        let uu____13579 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13579
                      else ());
                     (let uu____13584 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13584 with
                      | (u,_args) ->
                          let uu____13627 =
                            let uu____13628 = FStar_Syntax_Subst.compress u
                               in
                            uu____13628.FStar_Syntax_Syntax.n  in
                          (match uu____13627 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____13656 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13656 with
                                 | (u',uu____13675) ->
                                     let uu____13700 =
                                       let uu____13701 = whnf env u'  in
                                       uu____13701.FStar_Syntax_Syntax.n  in
                                     (match uu____13700 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13723 -> false)
                                  in
                               let uu____13725 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13748  ->
                                         match uu___23_13748 with
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
                                              | uu____13762 -> false)
                                         | uu____13766 -> false))
                                  in
                               (match uu____13725 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13781 = whnf env this_rigid
                                         in
                                      let uu____13782 =
                                        FStar_List.collect
                                          (fun uu___24_13788  ->
                                             match uu___24_13788 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13794 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13794]
                                             | uu____13798 -> [])
                                          bounds_probs
                                         in
                                      uu____13781 :: uu____13782  in
                                    let uu____13799 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13799 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13832 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13847 =
                                               let uu____13848 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13848.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13847 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13860 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13860)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13871 -> bound  in
                                           let uu____13872 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13872)  in
                                         (match uu____13832 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13907 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13907
                                                then
                                                  let wl'1 =
                                                    let uu___2019_13913 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2019_13913.wl_deferred);
                                                      ctr =
                                                        (uu___2019_13913.ctr);
                                                      defer_ok =
                                                        (uu___2019_13913.defer_ok);
                                                      smt_ok =
                                                        (uu___2019_13913.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2019_13913.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2019_13913.tcenv);
                                                      wl_implicits =
                                                        (uu___2019_13913.wl_implicits)
                                                    }  in
                                                  let uu____13914 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13914
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13920 =
                                                  solve_t env eq_prob
                                                    (let uu___2024_13922 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2024_13922.wl_deferred);
                                                       ctr =
                                                         (uu___2024_13922.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2024_13922.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2024_13922.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2024_13922.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13920 with
                                                | Success (uu____13924,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2030_13927 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2030_13927.wl_deferred);
                                                        ctr =
                                                          (uu___2030_13927.ctr);
                                                        defer_ok =
                                                          (uu___2030_13927.defer_ok);
                                                        smt_ok =
                                                          (uu___2030_13927.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2030_13927.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2030_13927.tcenv);
                                                        wl_implicits =
                                                          (uu___2030_13927.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2033_13929 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2033_13929.attempting);
                                                        wl_deferred =
                                                          (uu___2033_13929.wl_deferred);
                                                        ctr =
                                                          (uu___2033_13929.ctr);
                                                        defer_ok =
                                                          (uu___2033_13929.defer_ok);
                                                        smt_ok =
                                                          (uu___2033_13929.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2033_13929.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2033_13929.tcenv);
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
                                                    let uu____13945 =
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
                                                    ((let uu____13957 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13957
                                                      then
                                                        let uu____13962 =
                                                          let uu____13964 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13964
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13962
                                                      else ());
                                                     (let uu____13977 =
                                                        let uu____13992 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13992)
                                                         in
                                                      match uu____13977 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14014))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14040 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14040
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
                                                                  let uu____14060
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14060))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14085 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14085
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
                                                                    let uu____14105
                                                                    =
                                                                    let uu____14110
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14110
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14105
                                                                    [] wl2
                                                                     in
                                                                  let uu____14116
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14116))))
                                                      | uu____14117 ->
                                                          let uu____14132 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14132 p)))))))
                           | uu____14139 when flip ->
                               let uu____14140 =
                                 let uu____14142 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14144 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14142 uu____14144
                                  in
                               failwith uu____14140
                           | uu____14147 ->
                               let uu____14148 =
                                 let uu____14150 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14152 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14150 uu____14152
                                  in
                               failwith uu____14148)))))

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
                      (fun uu____14188  ->
                         match uu____14188 with
                         | (x,i) ->
                             let uu____14207 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14207, i)) bs_lhs
                     in
                  let uu____14210 = lhs  in
                  match uu____14210 with
                  | (uu____14211,u_lhs,uu____14213) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14310 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14320 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14320, univ)
                             in
                          match uu____14310 with
                          | (k,univ) ->
                              let uu____14327 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14327 with
                               | (uu____14344,u,wl3) ->
                                   let uu____14347 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14347, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14373 =
                              let uu____14386 =
                                let uu____14397 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14397 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14448  ->
                                   fun uu____14449  ->
                                     match (uu____14448, uu____14449) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14550 =
                                           let uu____14557 =
                                             let uu____14560 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14560
                                              in
                                           copy_uvar u_lhs [] uu____14557 wl2
                                            in
                                         (match uu____14550 with
                                          | (uu____14589,t_a,wl3) ->
                                              let uu____14592 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14592 with
                                               | (uu____14611,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14386
                                ([], wl1)
                               in
                            (match uu____14373 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2144_14667 = ct  in
                                   let uu____14668 =
                                     let uu____14671 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14671
                                      in
                                   let uu____14686 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2144_14667.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2144_14667.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14668;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14686;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2144_14667.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2147_14704 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2147_14704.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2147_14704.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14707 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____14707 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14745 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14745 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14756 =
                                          let uu____14761 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14761)  in
                                        TERM uu____14756  in
                                      let uu____14762 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14762 with
                                       | (sub_prob,wl3) ->
                                           let uu____14776 =
                                             let uu____14777 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14777
                                              in
                                           solve env uu____14776))
                             | (x,imp)::formals2 ->
                                 let uu____14799 =
                                   let uu____14806 =
                                     let uu____14809 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14809
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14806 wl1
                                    in
                                 (match uu____14799 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14830 =
                                          let uu____14833 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14833
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14830 u_x
                                         in
                                      let uu____14834 =
                                        let uu____14837 =
                                          let uu____14840 =
                                            let uu____14841 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14841, imp)  in
                                          [uu____14840]  in
                                        FStar_List.append bs_terms
                                          uu____14837
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14834 formals2 wl2)
                              in
                           let uu____14868 = occurs_check u_lhs arrow  in
                           (match uu____14868 with
                            | (uu____14881,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14897 =
                                    mklstr
                                      (fun uu____14902  ->
                                         let uu____14903 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14903)
                                     in
                                  giveup_or_defer env orig wl uu____14897
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
              (let uu____14936 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14936
               then
                 let uu____14941 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14944 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14941 (rel_to_string (p_rel orig)) uu____14944
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15075 = rhs wl1 scope env1 subst  in
                     (match uu____15075 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15098 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15098
                            then
                              let uu____15103 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15103
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15181 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15181 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2217_15183 = hd1  in
                       let uu____15184 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2217_15183.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2217_15183.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15184
                       }  in
                     let hd21 =
                       let uu___2220_15188 = hd2  in
                       let uu____15189 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2220_15188.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2220_15188.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15189
                       }  in
                     let uu____15192 =
                       let uu____15197 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15197
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15192 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15220 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15220
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15227 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15227 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15299 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15299
                                  in
                               ((let uu____15317 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15317
                                 then
                                   let uu____15322 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15324 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15322
                                     uu____15324
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15359 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15395 = aux wl [] env [] bs1 bs2  in
               match uu____15395 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15454 = attempt sub_probs wl2  in
                   solve env1 uu____15454)

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
            let uu___2258_15474 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2258_15474.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2258_15474.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15486 = try_solve env wl'  in
          match uu____15486 with
          | Success (uu____15487,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2267_15491 = wl  in
                  {
                    attempting = (uu___2267_15491.attempting);
                    wl_deferred = (uu___2267_15491.wl_deferred);
                    ctr = (uu___2267_15491.ctr);
                    defer_ok = (uu___2267_15491.defer_ok);
                    smt_ok = (uu___2267_15491.smt_ok);
                    umax_heuristic_ok = (uu___2267_15491.umax_heuristic_ok);
                    tcenv = (uu___2267_15491.tcenv);
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
        (let uu____15500 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15500 wl)

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
              let uu____15514 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15514 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15548 = lhs1  in
              match uu____15548 with
              | (uu____15551,ctx_u,uu____15553) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15561 ->
                        let uu____15562 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15562 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15611 = quasi_pattern env1 lhs1  in
              match uu____15611 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15645) ->
                  let uu____15650 = lhs1  in
                  (match uu____15650 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15665 = occurs_check ctx_u rhs1  in
                       (match uu____15665 with
                        | (uvars,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15716 =
                                let uu____15724 =
                                  let uu____15726 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15726
                                   in
                                FStar_Util.Inl uu____15724  in
                              (uu____15716, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15754 =
                                 let uu____15756 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15756  in
                               if uu____15754
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15783 =
                                    let uu____15791 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15791  in
                                  let uu____15797 =
                                    restrict_all_uvars ctx_u uvars wl1  in
                                  (uu____15783, uu____15797)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15841 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15841 with
              | (rhs_hd,args) ->
                  let uu____15884 = FStar_Util.prefix args  in
                  (match uu____15884 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15956 = lhs1  in
                       (match uu____15956 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15960 =
                              let uu____15971 =
                                let uu____15978 =
                                  let uu____15981 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15981
                                   in
                                copy_uvar u_lhs [] uu____15978 wl1  in
                              match uu____15971 with
                              | (uu____16008,t_last_arg,wl2) ->
                                  let uu____16011 =
                                    let uu____16018 =
                                      let uu____16019 =
                                        let uu____16028 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16028]  in
                                      FStar_List.append bs_lhs uu____16019
                                       in
                                    copy_uvar u_lhs uu____16018 t_res_lhs wl2
                                     in
                                  (match uu____16011 with
                                   | (uu____16063,lhs',wl3) ->
                                       let uu____16066 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16066 with
                                        | (uu____16083,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15960 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16104 =
                                     let uu____16105 =
                                       let uu____16110 =
                                         let uu____16111 =
                                           let uu____16114 =
                                             let uu____16119 =
                                               let uu____16120 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16120]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16119
                                              in
                                           uu____16114
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16111
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16110)  in
                                     TERM uu____16105  in
                                   [uu____16104]  in
                                 let uu____16145 =
                                   let uu____16152 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16152 with
                                   | (p1,wl3) ->
                                       let uu____16172 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16172 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16145 with
                                  | (sub_probs,wl3) ->
                                      let uu____16204 =
                                        let uu____16205 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16205  in
                                      solve env1 uu____16204))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16239 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16239 with
                | (uu____16257,args) ->
                    (match args with | [] -> false | uu____16293 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16312 =
                  let uu____16313 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16313.FStar_Syntax_Syntax.n  in
                match uu____16312 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16317 -> true
                | uu____16333 -> false  in
              let uu____16335 = quasi_pattern env1 lhs1  in
              match uu____16335 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16354  ->
                         let uu____16355 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16355)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16364 = is_app rhs1  in
                  if uu____16364
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16369 = is_arrow rhs1  in
                     if uu____16369
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16382  ->
                               let uu____16383 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16383)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16387 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16387
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16393 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16393
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16398 = lhs  in
                (match uu____16398 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16402 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16402 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16420 =
                              let uu____16424 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16424
                               in
                            FStar_All.pipe_right uu____16420
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16445 = occurs_check ctx_uv rhs1  in
                          (match uu____16445 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16474 =
                                   let uu____16475 =
                                     let uu____16477 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16477
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16475
                                    in
                                 giveup_or_defer env orig wl uu____16474
                               else
                                 (let uu____16485 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16485
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars wl  in
                                    let uu____16492 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16492
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16508  ->
                                              let uu____16509 =
                                                names_to_string1 fvs2  in
                                              let uu____16511 =
                                                names_to_string1 fvs1  in
                                              let uu____16513 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16509 uu____16511
                                                uu____16513)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16525 ->
                          if wl.defer_ok
                          then
                            let uu____16529 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16529
                          else
                            (let uu____16534 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16534 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16560 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16560
                             | (FStar_Util.Inl msg,uu____16562) ->
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
                  let uu____16580 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16580
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16586 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16586
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16608 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16608
                else
                  (let uu____16613 =
                     let uu____16630 = quasi_pattern env lhs  in
                     let uu____16637 = quasi_pattern env rhs  in
                     (uu____16630, uu____16637)  in
                   match uu____16613 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16680 = lhs  in
                       (match uu____16680 with
                        | ({ FStar_Syntax_Syntax.n = uu____16681;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16683;_},u_lhs,uu____16685)
                            ->
                            let uu____16688 = rhs  in
                            (match uu____16688 with
                             | (uu____16689,u_rhs,uu____16691) ->
                                 let uu____16692 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16692
                                 then
                                   let uu____16699 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16699
                                 else
                                   (let uu____16702 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16702 with
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
                                        let uu____16734 =
                                          let uu____16741 =
                                            let uu____16744 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16744
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16741
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16734 with
                                         | (uu____16756,w,wl1) ->
                                             let w_app =
                                               let uu____16762 =
                                                 let uu____16767 =
                                                   FStar_List.map
                                                     (fun uu____16778  ->
                                                        match uu____16778
                                                        with
                                                        | (z,uu____16786) ->
                                                            let uu____16791 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16791) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16767
                                                  in
                                               uu____16762
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16793 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16793
                                               then
                                                 let uu____16798 =
                                                   let uu____16802 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16804 =
                                                     let uu____16808 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16810 =
                                                       let uu____16814 =
                                                         term_to_string w  in
                                                       let uu____16816 =
                                                         let uu____16820 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16829 =
                                                           let uu____16833 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16842 =
                                                             let uu____16846
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16846]
                                                              in
                                                           uu____16833 ::
                                                             uu____16842
                                                            in
                                                         uu____16820 ::
                                                           uu____16829
                                                          in
                                                       uu____16814 ::
                                                         uu____16816
                                                        in
                                                     uu____16808 ::
                                                       uu____16810
                                                      in
                                                   uu____16802 :: uu____16804
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16798
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16863 =
                                                     let uu____16868 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16868)  in
                                                   TERM uu____16863  in
                                                 let uu____16869 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16869
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16877 =
                                                        let uu____16882 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16882)
                                                         in
                                                      TERM uu____16877  in
                                                    [s1; s2])
                                                  in
                                               let uu____16883 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16883))))))
                   | uu____16884 ->
                       let uu____16901 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16901)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16955 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16955
            then
              let uu____16960 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16962 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16964 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16966 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16960 uu____16962 uu____16964 uu____16966
            else ());
           (let uu____16977 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16977 with
            | (head1,args1) ->
                let uu____17020 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17020 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17090 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17090 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17095 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17095)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17116 =
                         mklstr
                           (fun uu____17127  ->
                              let uu____17128 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17130 = args_to_string args1  in
                              let uu____17134 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17136 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17128 uu____17130 uu____17134
                                uu____17136)
                          in
                       giveup env1 uu____17116 orig
                     else
                       (let uu____17143 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17148 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17148 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17143
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2523_17152 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2523_17152.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2523_17152.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2523_17152.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2523_17152.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2523_17152.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2523_17152.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2523_17152.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2523_17152.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17162 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17162
                                    else solve env1 wl2))
                        else
                          (let uu____17167 = base_and_refinement env1 t1  in
                           match uu____17167 with
                           | (base1,refinement1) ->
                               let uu____17192 = base_and_refinement env1 t2
                                  in
                               (match uu____17192 with
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
                                           let uu____17357 =
                                             FStar_List.fold_right
                                               (fun uu____17397  ->
                                                  fun uu____17398  ->
                                                    match (uu____17397,
                                                            uu____17398)
                                                    with
                                                    | (((a1,uu____17450),
                                                        (a2,uu____17452)),
                                                       (probs,wl3)) ->
                                                        let uu____17501 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17501
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17357 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17544 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17544
                                                 then
                                                   let uu____17549 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17549
                                                 else ());
                                                (let uu____17555 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17555
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
                                                    (let uu____17582 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17582 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17598 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17598
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17606 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17606))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17631 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17631 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17647 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17647
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17655 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17655)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17683 =
                                           match uu____17683 with
                                           | (prob,reason) ->
                                               ((let uu____17700 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17700
                                                 then
                                                   let uu____17705 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17707 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17705 uu____17707
                                                 else ());
                                                (let uu____17713 =
                                                   let uu____17722 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17725 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17722, uu____17725)
                                                    in
                                                 match uu____17713 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17738 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17738 with
                                                      | (head1',uu____17756)
                                                          ->
                                                          let uu____17781 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17781
                                                           with
                                                           | (head2',uu____17799)
                                                               ->
                                                               let uu____17824
                                                                 =
                                                                 let uu____17829
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17830
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17829,
                                                                   uu____17830)
                                                                  in
                                                               (match uu____17824
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17832
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17832
                                                                    then
                                                                    let uu____17837
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17839
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17841
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17843
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17837
                                                                    uu____17839
                                                                    uu____17841
                                                                    uu____17843
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17848
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2611_17856
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2611_17856.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2611_17856.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2611_17856.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2611_17856.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2611_17856.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2611_17856.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2611_17856.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2611_17856.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17858
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17858
                                                                    then
                                                                    let uu____17863
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17863
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17868 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17880 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17880 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17888 =
                                             let uu____17889 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17889.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17888 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17894 -> false  in
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
                                          | uu____17897 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17900 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2631_17936 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2631_17936.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2631_17936.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2631_17936.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2631_17936.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2631_17936.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2631_17936.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2631_17936.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2631_17936.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18012 = destruct_flex_t scrutinee wl1  in
             match uu____18012 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18023 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18023 with
                  | (xs,pat_term,uu____18039,uu____18040) ->
                      let uu____18045 =
                        FStar_List.fold_left
                          (fun uu____18068  ->
                             fun x  ->
                               match uu____18068 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18089 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18089 with
                                    | (uu____18108,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18045 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18129 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18129 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2671_18146 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2671_18146.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2671_18146.umax_heuristic_ok);
                                    tcenv = (uu___2671_18146.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18157 = solve env1 wl'  in
                                (match uu____18157 with
                                 | Success (uu____18160,imps) ->
                                     let wl'1 =
                                       let uu___2679_18163 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2679_18163.wl_deferred);
                                         ctr = (uu___2679_18163.ctr);
                                         defer_ok =
                                           (uu___2679_18163.defer_ok);
                                         smt_ok = (uu___2679_18163.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2679_18163.umax_heuristic_ok);
                                         tcenv = (uu___2679_18163.tcenv);
                                         wl_implicits =
                                           (uu___2679_18163.wl_implicits)
                                       }  in
                                     let uu____18164 = solve env1 wl'1  in
                                     (match uu____18164 with
                                      | Success (uu____18167,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2687_18171 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2687_18171.attempting);
                                                 wl_deferred =
                                                   (uu___2687_18171.wl_deferred);
                                                 ctr = (uu___2687_18171.ctr);
                                                 defer_ok =
                                                   (uu___2687_18171.defer_ok);
                                                 smt_ok =
                                                   (uu___2687_18171.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2687_18171.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2687_18171.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18172 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18178 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18201 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18201
                 then
                   let uu____18206 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18208 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18206 uu____18208
                 else ());
                (let uu____18213 =
                   let uu____18234 =
                     let uu____18243 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18243)  in
                   let uu____18250 =
                     let uu____18259 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18259)  in
                   (uu____18234, uu____18250)  in
                 match uu____18213 with
                 | ((uu____18289,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18292;
                                   FStar_Syntax_Syntax.vars = uu____18293;_}),
                    (s,t)) ->
                     let uu____18364 =
                       let uu____18366 = is_flex scrutinee  in
                       Prims.op_Negation uu____18366  in
                     if uu____18364
                     then
                       ((let uu____18377 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18377
                         then
                           let uu____18382 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18382
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18401 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18401
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18416 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18416
                           then
                             let uu____18421 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18423 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18421 uu____18423
                           else ());
                          (let pat_discriminates uu___25_18448 =
                             match uu___25_18448 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18464;
                                  FStar_Syntax_Syntax.p = uu____18465;_},FStar_Pervasives_Native.None
                                ,uu____18466) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18480;
                                  FStar_Syntax_Syntax.p = uu____18481;_},FStar_Pervasives_Native.None
                                ,uu____18482) -> true
                             | uu____18509 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18612 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18612 with
                                       | (uu____18614,uu____18615,t') ->
                                           let uu____18633 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18633 with
                                            | (FullMatch ,uu____18645) ->
                                                true
                                            | (HeadMatch
                                               uu____18659,uu____18660) ->
                                                true
                                            | uu____18675 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18712 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18712
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18723 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18723 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18811,uu____18812) ->
                                       branches1
                                   | uu____18957 -> branches  in
                                 let uu____19012 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19021 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19021 with
                                        | (p,uu____19025,uu____19026) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19055  ->
                                      FStar_Util.Inr uu____19055) uu____19012))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19085 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19085 with
                                | (p,uu____19094,e) ->
                                    ((let uu____19113 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19113
                                      then
                                        let uu____19118 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19120 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19118 uu____19120
                                      else ());
                                     (let uu____19125 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19140  ->
                                           FStar_Util.Inr uu____19140)
                                        uu____19125)))))
                 | ((s,t),(uu____19143,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19146;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19147;_}))
                     ->
                     let uu____19216 =
                       let uu____19218 = is_flex scrutinee  in
                       Prims.op_Negation uu____19218  in
                     if uu____19216
                     then
                       ((let uu____19229 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19229
                         then
                           let uu____19234 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19234
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19253 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19253
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19268 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19268
                           then
                             let uu____19273 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19275 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19273 uu____19275
                           else ());
                          (let pat_discriminates uu___25_19300 =
                             match uu___25_19300 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19316;
                                  FStar_Syntax_Syntax.p = uu____19317;_},FStar_Pervasives_Native.None
                                ,uu____19318) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19332;
                                  FStar_Syntax_Syntax.p = uu____19333;_},FStar_Pervasives_Native.None
                                ,uu____19334) -> true
                             | uu____19361 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19464 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19464 with
                                       | (uu____19466,uu____19467,t') ->
                                           let uu____19485 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19485 with
                                            | (FullMatch ,uu____19497) ->
                                                true
                                            | (HeadMatch
                                               uu____19511,uu____19512) ->
                                                true
                                            | uu____19527 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19564 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19564
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19575 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19575 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19663,uu____19664) ->
                                       branches1
                                   | uu____19809 -> branches  in
                                 let uu____19864 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19873 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19873 with
                                        | (p,uu____19877,uu____19878) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19907  ->
                                      FStar_Util.Inr uu____19907) uu____19864))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19937 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19937 with
                                | (p,uu____19946,e) ->
                                    ((let uu____19965 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19965
                                      then
                                        let uu____19970 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19972 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19970 uu____19972
                                      else ());
                                     (let uu____19977 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19992  ->
                                           FStar_Util.Inr uu____19992)
                                        uu____19977)))))
                 | uu____19993 ->
                     ((let uu____20015 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20015
                       then
                         let uu____20020 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20022 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20020 uu____20022
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20068 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20068
            then
              let uu____20073 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20075 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20077 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20079 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20073 uu____20075 uu____20077 uu____20079
            else ());
           (let uu____20084 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20084 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20115,uu____20116) ->
                     let rec may_relate head =
                       let uu____20144 =
                         let uu____20145 = FStar_Syntax_Subst.compress head
                            in
                         uu____20145.FStar_Syntax_Syntax.n  in
                       match uu____20144 with
                       | FStar_Syntax_Syntax.Tm_name uu____20149 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20151 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20176 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20176 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20178 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20181
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20182 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20185,uu____20186) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20228) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20234) ->
                           may_relate t
                       | uu____20239 -> false  in
                     let uu____20241 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20241 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20254 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20254
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20264 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20264
                          then
                            let uu____20267 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20267 with
                             | (guard,wl2) ->
                                 let uu____20274 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20274)
                          else
                            (let uu____20277 =
                               mklstr
                                 (fun uu____20288  ->
                                    let uu____20289 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20291 =
                                      let uu____20293 =
                                        let uu____20297 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20297
                                          (fun x  ->
                                             let uu____20304 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20304)
                                         in
                                      FStar_Util.dflt "" uu____20293  in
                                    let uu____20309 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20311 =
                                      let uu____20313 =
                                        let uu____20317 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20317
                                          (fun x  ->
                                             let uu____20324 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20324)
                                         in
                                      FStar_Util.dflt "" uu____20313  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20289 uu____20291 uu____20309
                                      uu____20311)
                                in
                             giveup env1 uu____20277 orig))
                 | (HeadMatch (true ),uu____20330) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20345 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20345 with
                        | (guard,wl2) ->
                            let uu____20352 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20352)
                     else
                       (let uu____20355 =
                          mklstr
                            (fun uu____20362  ->
                               let uu____20363 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20365 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20363 uu____20365)
                           in
                        giveup env1 uu____20355 orig)
                 | (uu____20368,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2862_20382 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2862_20382.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2862_20382.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2862_20382.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2862_20382.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2862_20382.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2862_20382.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2862_20382.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2862_20382.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20409 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20409
          then
            let uu____20412 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20412
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20418 =
                let uu____20421 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20421  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20418 t1);
             (let uu____20440 =
                let uu____20443 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20443  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20440 t2);
             (let uu____20462 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20462
              then
                let uu____20466 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20468 =
                  let uu____20470 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20472 =
                    let uu____20474 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20474  in
                  Prims.op_Hat uu____20470 uu____20472  in
                let uu____20477 =
                  let uu____20479 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20481 =
                    let uu____20483 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20483  in
                  Prims.op_Hat uu____20479 uu____20481  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20466 uu____20468 uu____20477
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20490,uu____20491) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20507,FStar_Syntax_Syntax.Tm_delayed uu____20508) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20524,uu____20525) ->
                  let uu____20552 =
                    let uu___2893_20553 = problem  in
                    let uu____20554 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2893_20553.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20554;
                      FStar_TypeChecker_Common.relation =
                        (uu___2893_20553.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2893_20553.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2893_20553.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2893_20553.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2893_20553.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2893_20553.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2893_20553.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2893_20553.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20552 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20555,uu____20556) ->
                  let uu____20563 =
                    let uu___2899_20564 = problem  in
                    let uu____20565 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2899_20564.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20565;
                      FStar_TypeChecker_Common.relation =
                        (uu___2899_20564.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2899_20564.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2899_20564.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2899_20564.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2899_20564.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2899_20564.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2899_20564.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2899_20564.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20563 wl
              | (uu____20566,FStar_Syntax_Syntax.Tm_ascribed uu____20567) ->
                  let uu____20594 =
                    let uu___2905_20595 = problem  in
                    let uu____20596 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2905_20595.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2905_20595.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2905_20595.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20596;
                      FStar_TypeChecker_Common.element =
                        (uu___2905_20595.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2905_20595.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2905_20595.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2905_20595.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2905_20595.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2905_20595.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20594 wl
              | (uu____20597,FStar_Syntax_Syntax.Tm_meta uu____20598) ->
                  let uu____20605 =
                    let uu___2911_20606 = problem  in
                    let uu____20607 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2911_20606.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2911_20606.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2911_20606.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20607;
                      FStar_TypeChecker_Common.element =
                        (uu___2911_20606.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2911_20606.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2911_20606.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2911_20606.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2911_20606.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2911_20606.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20605 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20609),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20611)) ->
                  let uu____20620 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20620
              | (FStar_Syntax_Syntax.Tm_bvar uu____20621,uu____20622) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20624,FStar_Syntax_Syntax.Tm_bvar uu____20625) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___26_20695 =
                    match uu___26_20695 with
                    | [] -> c
                    | bs ->
                        let uu____20723 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20723
                     in
                  let uu____20734 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20734 with
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
                                    let uu____20883 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20883
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
                  let mk_t t l uu___27_20972 =
                    match uu___27_20972 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21014 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21014 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21159 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21160 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21159
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21160 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21162,uu____21163) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21194 -> true
                    | uu____21214 -> false  in
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
                      (let uu____21274 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3013_21282 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3013_21282.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3013_21282.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3013_21282.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3013_21282.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3013_21282.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3013_21282.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3013_21282.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3013_21282.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3013_21282.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3013_21282.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3013_21282.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3013_21282.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3013_21282.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3013_21282.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3013_21282.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3013_21282.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3013_21282.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3013_21282.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3013_21282.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3013_21282.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3013_21282.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3013_21282.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3013_21282.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3013_21282.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3013_21282.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3013_21282.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3013_21282.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3013_21282.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3013_21282.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3013_21282.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3013_21282.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3013_21282.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3013_21282.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3013_21282.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3013_21282.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3013_21282.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3013_21282.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3013_21282.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3013_21282.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3013_21282.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3013_21282.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3013_21282.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3013_21282.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21274 with
                       | (uu____21287,ty,uu____21289) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21298 =
                                 let uu____21299 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21299.FStar_Syntax_Syntax.n  in
                               match uu____21298 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21302 ->
                                   let uu____21309 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21309
                               | uu____21310 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21313 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21313
                             then
                               let uu____21318 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21320 =
                                 let uu____21322 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21322
                                  in
                               let uu____21323 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21318 uu____21320 uu____21323
                             else ());
                            r1))
                     in
                  let uu____21328 =
                    let uu____21345 = maybe_eta t1  in
                    let uu____21352 = maybe_eta t2  in
                    (uu____21345, uu____21352)  in
                  (match uu____21328 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3034_21394 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3034_21394.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3034_21394.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3034_21394.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3034_21394.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3034_21394.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3034_21394.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3034_21394.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3034_21394.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21415 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21415
                       then
                         let uu____21418 = destruct_flex_t not_abs wl  in
                         (match uu____21418 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21435 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21435.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21435.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21435.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21435.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21435.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21435.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21435.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21435.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21438 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21438 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21461 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21461
                       then
                         let uu____21464 = destruct_flex_t not_abs wl  in
                         (match uu____21464 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21481 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21481.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21481.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21481.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21481.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21481.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21481.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21481.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21481.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21484 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21484 orig))
                   | uu____21487 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21505,FStar_Syntax_Syntax.Tm_abs uu____21506) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21537 -> true
                    | uu____21557 -> false  in
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
                      (let uu____21617 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3013_21625 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3013_21625.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3013_21625.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3013_21625.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3013_21625.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3013_21625.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3013_21625.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3013_21625.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3013_21625.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3013_21625.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3013_21625.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3013_21625.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3013_21625.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3013_21625.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3013_21625.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3013_21625.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3013_21625.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3013_21625.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3013_21625.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3013_21625.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3013_21625.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3013_21625.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3013_21625.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3013_21625.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3013_21625.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3013_21625.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3013_21625.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3013_21625.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3013_21625.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3013_21625.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3013_21625.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3013_21625.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3013_21625.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3013_21625.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3013_21625.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3013_21625.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3013_21625.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3013_21625.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3013_21625.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3013_21625.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3013_21625.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3013_21625.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3013_21625.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3013_21625.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21617 with
                       | (uu____21630,ty,uu____21632) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21641 =
                                 let uu____21642 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21642.FStar_Syntax_Syntax.n  in
                               match uu____21641 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21645 ->
                                   let uu____21652 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21652
                               | uu____21653 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21656 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21656
                             then
                               let uu____21661 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21663 =
                                 let uu____21665 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21665
                                  in
                               let uu____21666 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21661 uu____21663 uu____21666
                             else ());
                            r1))
                     in
                  let uu____21671 =
                    let uu____21688 = maybe_eta t1  in
                    let uu____21695 = maybe_eta t2  in
                    (uu____21688, uu____21695)  in
                  (match uu____21671 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3034_21737 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3034_21737.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3034_21737.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3034_21737.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3034_21737.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3034_21737.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3034_21737.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3034_21737.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3034_21737.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21758 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21758
                       then
                         let uu____21761 = destruct_flex_t not_abs wl  in
                         (match uu____21761 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21778 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21778.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21778.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21778.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21778.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21778.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21778.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21778.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21778.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21781 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21781 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21804 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21804
                       then
                         let uu____21807 = destruct_flex_t not_abs wl  in
                         (match uu____21807 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21824 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21824.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21824.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21824.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21824.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21824.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21824.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21824.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21824.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21827 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21827 orig))
                   | uu____21830 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21860 =
                    let uu____21865 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21865 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3074_21893 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3074_21893.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3074_21893.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3076_21895 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3076_21895.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3076_21895.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21896,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3074_21911 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3074_21911.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3074_21911.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3076_21913 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3076_21913.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3076_21913.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21914 -> (x1, x2)  in
                  (match uu____21860 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21933 = as_refinement false env t11  in
                       (match uu____21933 with
                        | (x12,phi11) ->
                            let uu____21941 = as_refinement false env t21  in
                            (match uu____21941 with
                             | (x22,phi21) ->
                                 ((let uu____21950 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21950
                                   then
                                     ((let uu____21955 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21957 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21959 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21955
                                         uu____21957 uu____21959);
                                      (let uu____21962 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21964 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21966 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21962
                                         uu____21964 uu____21966))
                                   else ());
                                  (let uu____21971 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21971 with
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
                                         let uu____22042 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22042
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22054 =
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
                                         (let uu____22067 =
                                            let uu____22070 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22070
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22067
                                            (p_guard base_prob));
                                         (let uu____22089 =
                                            let uu____22092 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22092
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22089
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22111 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22111)
                                          in
                                       let has_uvars =
                                         (let uu____22116 =
                                            let uu____22118 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22118
                                             in
                                          Prims.op_Negation uu____22116) ||
                                           (let uu____22122 =
                                              let uu____22124 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22124
                                               in
                                            Prims.op_Negation uu____22122)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22128 =
                                           let uu____22133 =
                                             let uu____22142 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22142]  in
                                           mk_t_problem wl1 uu____22133 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22128 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22165 =
                                                solve env1
                                                  (let uu___3119_22167 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3119_22167.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3119_22167.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3119_22167.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3119_22167.tcenv);
                                                     wl_implicits =
                                                       (uu___3119_22167.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22165 with
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
                                               | Success uu____22182 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22191 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22191
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3132_22200 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3132_22200.attempting);
                                                         wl_deferred =
                                                           (uu___3132_22200.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3132_22200.defer_ok);
                                                         smt_ok =
                                                           (uu___3132_22200.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3132_22200.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3132_22200.tcenv);
                                                         wl_implicits =
                                                           (uu___3132_22200.wl_implicits)
                                                       }  in
                                                     let uu____22202 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22202))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22205,FStar_Syntax_Syntax.Tm_uvar uu____22206) ->
                  let uu____22231 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22231 with
                   | (t11,wl1) ->
                       let uu____22238 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22238 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22247;
                    FStar_Syntax_Syntax.pos = uu____22248;
                    FStar_Syntax_Syntax.vars = uu____22249;_},uu____22250),FStar_Syntax_Syntax.Tm_uvar
                 uu____22251) ->
                  let uu____22300 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22300 with
                   | (t11,wl1) ->
                       let uu____22307 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22307 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22316,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22317;
                    FStar_Syntax_Syntax.pos = uu____22318;
                    FStar_Syntax_Syntax.vars = uu____22319;_},uu____22320))
                  ->
                  let uu____22369 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22369 with
                   | (t11,wl1) ->
                       let uu____22376 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22376 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22385;
                    FStar_Syntax_Syntax.pos = uu____22386;
                    FStar_Syntax_Syntax.vars = uu____22387;_},uu____22388),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22389;
                    FStar_Syntax_Syntax.pos = uu____22390;
                    FStar_Syntax_Syntax.vars = uu____22391;_},uu____22392))
                  ->
                  let uu____22465 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22465 with
                   | (t11,wl1) ->
                       let uu____22472 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22472 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22481,uu____22482) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22495 = destruct_flex_t t1 wl  in
                  (match uu____22495 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22502;
                    FStar_Syntax_Syntax.pos = uu____22503;
                    FStar_Syntax_Syntax.vars = uu____22504;_},uu____22505),uu____22506)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22543 = destruct_flex_t t1 wl  in
                  (match uu____22543 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22550,FStar_Syntax_Syntax.Tm_uvar uu____22551) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22564,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22565;
                    FStar_Syntax_Syntax.pos = uu____22566;
                    FStar_Syntax_Syntax.vars = uu____22567;_},uu____22568))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22605,FStar_Syntax_Syntax.Tm_arrow uu____22606) ->
                  solve_t' env
                    (let uu___3234_22634 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3234_22634.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3234_22634.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3234_22634.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3234_22634.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3234_22634.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3234_22634.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3234_22634.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3234_22634.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3234_22634.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22635;
                    FStar_Syntax_Syntax.pos = uu____22636;
                    FStar_Syntax_Syntax.vars = uu____22637;_},uu____22638),FStar_Syntax_Syntax.Tm_arrow
                 uu____22639) ->
                  solve_t' env
                    (let uu___3234_22691 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3234_22691.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3234_22691.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3234_22691.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3234_22691.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3234_22691.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3234_22691.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3234_22691.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3234_22691.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3234_22691.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22692,FStar_Syntax_Syntax.Tm_uvar uu____22693) ->
                  let uu____22706 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22706
              | (uu____22707,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22708;
                    FStar_Syntax_Syntax.pos = uu____22709;
                    FStar_Syntax_Syntax.vars = uu____22710;_},uu____22711))
                  ->
                  let uu____22748 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22748
              | (FStar_Syntax_Syntax.Tm_uvar uu____22749,uu____22750) ->
                  let uu____22763 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22763
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22764;
                    FStar_Syntax_Syntax.pos = uu____22765;
                    FStar_Syntax_Syntax.vars = uu____22766;_},uu____22767),uu____22768)
                  ->
                  let uu____22805 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22805
              | (FStar_Syntax_Syntax.Tm_refine uu____22806,uu____22807) ->
                  let t21 =
                    let uu____22815 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22815  in
                  solve_t env
                    (let uu___3269_22841 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3269_22841.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3269_22841.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3269_22841.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3269_22841.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3269_22841.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3269_22841.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3269_22841.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3269_22841.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3269_22841.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22842,FStar_Syntax_Syntax.Tm_refine uu____22843) ->
                  let t11 =
                    let uu____22851 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22851  in
                  solve_t env
                    (let uu___3276_22877 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3276_22877.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3276_22877.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3276_22877.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3276_22877.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3276_22877.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3276_22877.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3276_22877.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3276_22877.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3276_22877.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22959 =
                    let uu____22960 = guard_of_prob env wl problem t1 t2  in
                    match uu____22960 with
                    | (guard,wl1) ->
                        let uu____22967 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22967
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23186 = br1  in
                        (match uu____23186 with
                         | (p1,w1,uu____23215) ->
                             let uu____23232 = br2  in
                             (match uu____23232 with
                              | (p2,w2,uu____23255) ->
                                  let uu____23260 =
                                    let uu____23262 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23262  in
                                  if uu____23260
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23289 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23289 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23326 = br2  in
                                         (match uu____23326 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23359 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23359
                                                 in
                                              let uu____23364 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23395,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23416) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23475 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23475 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23364
                                                (fun uu____23547  ->
                                                   match uu____23547 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23584 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23584
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23605
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23605
                                                              then
                                                                let uu____23610
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23612
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23610
                                                                  uu____23612
                                                              else ());
                                                             (let uu____23618
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23618
                                                                (fun
                                                                   uu____23654
                                                                    ->
                                                                   match uu____23654
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
                    | uu____23783 -> FStar_Pervasives_Native.None  in
                  let uu____23824 = solve_branches wl brs1 brs2  in
                  (match uu____23824 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23850 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23850 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23877 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23877 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23911 =
                                FStar_List.map
                                  (fun uu____23923  ->
                                     match uu____23923 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23911  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23932 =
                              let uu____23933 =
                                let uu____23934 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23934
                                  (let uu___3375_23942 = wl3  in
                                   {
                                     attempting =
                                       (uu___3375_23942.attempting);
                                     wl_deferred =
                                       (uu___3375_23942.wl_deferred);
                                     ctr = (uu___3375_23942.ctr);
                                     defer_ok = (uu___3375_23942.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3375_23942.umax_heuristic_ok);
                                     tcenv = (uu___3375_23942.tcenv);
                                     wl_implicits =
                                       (uu___3375_23942.wl_implicits)
                                   })
                                 in
                              solve env uu____23933  in
                            (match uu____23932 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23947 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23956 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23956 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23959,uu____23960) ->
                  let head1 =
                    let uu____23984 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23984
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24030 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24030
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24076 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24076
                    then
                      let uu____24080 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24082 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24084 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24080 uu____24082 uu____24084
                    else ());
                   (let no_free_uvars t =
                      (let uu____24098 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24098) &&
                        (let uu____24102 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24102)
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
                      let uu____24121 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24121 = FStar_Syntax_Util.Equal  in
                    let uu____24122 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24122
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24126 = equal t1 t2  in
                         (if uu____24126
                          then
                            let uu____24129 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24129
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24134 =
                            let uu____24141 = equal t1 t2  in
                            if uu____24141
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24154 = mk_eq2 wl env orig t1 t2  in
                               match uu____24154 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24134 with
                          | (guard,wl1) ->
                              let uu____24175 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24175))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24178,uu____24179) ->
                  let head1 =
                    let uu____24187 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24187
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24233 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24233
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24279 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24279
                    then
                      let uu____24283 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24285 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24287 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24283 uu____24285 uu____24287
                    else ());
                   (let no_free_uvars t =
                      (let uu____24301 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24301) &&
                        (let uu____24305 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24305)
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
                      let uu____24324 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24324 = FStar_Syntax_Util.Equal  in
                    let uu____24325 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24325
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24329 = equal t1 t2  in
                         (if uu____24329
                          then
                            let uu____24332 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24332
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24337 =
                            let uu____24344 = equal t1 t2  in
                            if uu____24344
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24357 = mk_eq2 wl env orig t1 t2  in
                               match uu____24357 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24337 with
                          | (guard,wl1) ->
                              let uu____24378 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24378))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24381,uu____24382) ->
                  let head1 =
                    let uu____24384 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24384
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24430 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24430
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24476 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24476
                    then
                      let uu____24480 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24482 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24484 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24480 uu____24482 uu____24484
                    else ());
                   (let no_free_uvars t =
                      (let uu____24498 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24498) &&
                        (let uu____24502 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24502)
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
                      let uu____24521 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24521 = FStar_Syntax_Util.Equal  in
                    let uu____24522 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24522
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24526 = equal t1 t2  in
                         (if uu____24526
                          then
                            let uu____24529 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24529
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24534 =
                            let uu____24541 = equal t1 t2  in
                            if uu____24541
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24554 = mk_eq2 wl env orig t1 t2  in
                               match uu____24554 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24534 with
                          | (guard,wl1) ->
                              let uu____24575 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24575))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24578,uu____24579) ->
                  let head1 =
                    let uu____24581 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24581
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24627 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24627
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24673 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24673
                    then
                      let uu____24677 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24679 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24681 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24677 uu____24679 uu____24681
                    else ());
                   (let no_free_uvars t =
                      (let uu____24695 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24695) &&
                        (let uu____24699 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24699)
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
                      let uu____24718 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24718 = FStar_Syntax_Util.Equal  in
                    let uu____24719 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24719
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24723 = equal t1 t2  in
                         (if uu____24723
                          then
                            let uu____24726 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24726
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24731 =
                            let uu____24738 = equal t1 t2  in
                            if uu____24738
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24751 = mk_eq2 wl env orig t1 t2  in
                               match uu____24751 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24731 with
                          | (guard,wl1) ->
                              let uu____24772 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24772))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24775,uu____24776) ->
                  let head1 =
                    let uu____24778 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24778
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24824 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24824
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24870 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24870
                    then
                      let uu____24874 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24876 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24878 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24874 uu____24876 uu____24878
                    else ());
                   (let no_free_uvars t =
                      (let uu____24892 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24892) &&
                        (let uu____24896 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24896)
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
                      let uu____24915 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24915 = FStar_Syntax_Util.Equal  in
                    let uu____24916 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24916
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24920 = equal t1 t2  in
                         (if uu____24920
                          then
                            let uu____24923 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24923
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24928 =
                            let uu____24935 = equal t1 t2  in
                            if uu____24935
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24948 = mk_eq2 wl env orig t1 t2  in
                               match uu____24948 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24928 with
                          | (guard,wl1) ->
                              let uu____24969 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24969))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24972,uu____24973) ->
                  let head1 =
                    let uu____24991 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24991
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25037 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25037
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25083 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25083
                    then
                      let uu____25087 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25089 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25091 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25087 uu____25089 uu____25091
                    else ());
                   (let no_free_uvars t =
                      (let uu____25105 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25105) &&
                        (let uu____25109 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25109)
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
                      let uu____25128 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25128 = FStar_Syntax_Util.Equal  in
                    let uu____25129 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25129
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25133 = equal t1 t2  in
                         (if uu____25133
                          then
                            let uu____25136 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25136
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25141 =
                            let uu____25148 = equal t1 t2  in
                            if uu____25148
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25161 = mk_eq2 wl env orig t1 t2  in
                               match uu____25161 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25141 with
                          | (guard,wl1) ->
                              let uu____25182 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25182))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25185,FStar_Syntax_Syntax.Tm_match uu____25186) ->
                  let head1 =
                    let uu____25210 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25210
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25256 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25256
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25302 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25302
                    then
                      let uu____25306 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25308 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25310 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25306 uu____25308 uu____25310
                    else ());
                   (let no_free_uvars t =
                      (let uu____25324 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25324) &&
                        (let uu____25328 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25328)
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
                      let uu____25347 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25347 = FStar_Syntax_Util.Equal  in
                    let uu____25348 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25348
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25352 = equal t1 t2  in
                         (if uu____25352
                          then
                            let uu____25355 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25355
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25360 =
                            let uu____25367 = equal t1 t2  in
                            if uu____25367
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25380 = mk_eq2 wl env orig t1 t2  in
                               match uu____25380 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25360 with
                          | (guard,wl1) ->
                              let uu____25401 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25401))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25404,FStar_Syntax_Syntax.Tm_uinst uu____25405) ->
                  let head1 =
                    let uu____25413 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25413
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25459 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25459
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25505 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25505
                    then
                      let uu____25509 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25511 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25513 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25509 uu____25511 uu____25513
                    else ());
                   (let no_free_uvars t =
                      (let uu____25527 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25527) &&
                        (let uu____25531 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25531)
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
                      let uu____25550 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25550 = FStar_Syntax_Util.Equal  in
                    let uu____25551 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25551
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25555 = equal t1 t2  in
                         (if uu____25555
                          then
                            let uu____25558 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25558
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25563 =
                            let uu____25570 = equal t1 t2  in
                            if uu____25570
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25583 = mk_eq2 wl env orig t1 t2  in
                               match uu____25583 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25563 with
                          | (guard,wl1) ->
                              let uu____25604 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25604))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25607,FStar_Syntax_Syntax.Tm_name uu____25608) ->
                  let head1 =
                    let uu____25610 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25610
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25656 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25656
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25696 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25696
                    then
                      let uu____25700 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25702 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25704 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25700 uu____25702 uu____25704
                    else ());
                   (let no_free_uvars t =
                      (let uu____25718 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25718) &&
                        (let uu____25722 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25722)
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
                      let uu____25741 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25741 = FStar_Syntax_Util.Equal  in
                    let uu____25742 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25742
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25746 = equal t1 t2  in
                         (if uu____25746
                          then
                            let uu____25749 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25749
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25754 =
                            let uu____25761 = equal t1 t2  in
                            if uu____25761
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25774 = mk_eq2 wl env orig t1 t2  in
                               match uu____25774 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25754 with
                          | (guard,wl1) ->
                              let uu____25795 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25795))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25798,FStar_Syntax_Syntax.Tm_constant uu____25799) ->
                  let head1 =
                    let uu____25801 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25801
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25841 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25841
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25881 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25881
                    then
                      let uu____25885 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25887 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25889 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25885 uu____25887 uu____25889
                    else ());
                   (let no_free_uvars t =
                      (let uu____25903 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25903) &&
                        (let uu____25907 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25907)
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
                      let uu____25926 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25926 = FStar_Syntax_Util.Equal  in
                    let uu____25927 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25927
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25931 = equal t1 t2  in
                         (if uu____25931
                          then
                            let uu____25934 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25934
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25939 =
                            let uu____25946 = equal t1 t2  in
                            if uu____25946
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25959 = mk_eq2 wl env orig t1 t2  in
                               match uu____25959 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25939 with
                          | (guard,wl1) ->
                              let uu____25980 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25980))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25983,FStar_Syntax_Syntax.Tm_fvar uu____25984) ->
                  let head1 =
                    let uu____25986 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25986
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26032 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26032
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26078 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26078
                    then
                      let uu____26082 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26084 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26086 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26082 uu____26084 uu____26086
                    else ());
                   (let no_free_uvars t =
                      (let uu____26100 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26100) &&
                        (let uu____26104 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26104)
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
                      let uu____26123 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26123 = FStar_Syntax_Util.Equal  in
                    let uu____26124 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26124
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26128 = equal t1 t2  in
                         (if uu____26128
                          then
                            let uu____26131 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26131
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26136 =
                            let uu____26143 = equal t1 t2  in
                            if uu____26143
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26156 = mk_eq2 wl env orig t1 t2  in
                               match uu____26156 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26136 with
                          | (guard,wl1) ->
                              let uu____26177 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26177))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26180,FStar_Syntax_Syntax.Tm_app uu____26181) ->
                  let head1 =
                    let uu____26199 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26199
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26239 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26239
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26279 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26279
                    then
                      let uu____26283 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26285 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26287 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26283 uu____26285 uu____26287
                    else ());
                   (let no_free_uvars t =
                      (let uu____26301 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26301) &&
                        (let uu____26305 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26305)
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
                      let uu____26324 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26324 = FStar_Syntax_Util.Equal  in
                    let uu____26325 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26325
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26329 = equal t1 t2  in
                         (if uu____26329
                          then
                            let uu____26332 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26332
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26337 =
                            let uu____26344 = equal t1 t2  in
                            if uu____26344
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26357 = mk_eq2 wl env orig t1 t2  in
                               match uu____26357 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26337 with
                          | (guard,wl1) ->
                              let uu____26378 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26378))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26381,FStar_Syntax_Syntax.Tm_let uu____26382) ->
                  let uu____26409 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26409
                  then
                    let uu____26412 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26412
                  else
                    (let uu____26415 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26415 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26418,uu____26419) ->
                  let uu____26433 =
                    let uu____26439 =
                      let uu____26441 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26443 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26445 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26447 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26441 uu____26443 uu____26445 uu____26447
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26439)
                     in
                  FStar_Errors.raise_error uu____26433
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26451,FStar_Syntax_Syntax.Tm_let uu____26452) ->
                  let uu____26466 =
                    let uu____26472 =
                      let uu____26474 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26476 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26478 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26480 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26474 uu____26476 uu____26478 uu____26480
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26472)
                     in
                  FStar_Errors.raise_error uu____26466
                    t1.FStar_Syntax_Syntax.pos
              | uu____26484 ->
                  let uu____26489 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26489 orig))))

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
          (let uu____26555 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26555
           then
             let uu____26560 =
               let uu____26562 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26562  in
             let uu____26563 =
               let uu____26565 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26565  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26560 uu____26563
           else ());
          (let uu____26569 =
             let uu____26571 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26571  in
           if uu____26569
           then
             let uu____26574 =
               mklstr
                 (fun uu____26581  ->
                    let uu____26582 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26584 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26582 uu____26584)
                in
             giveup env uu____26574 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26606 =
                  mklstr
                    (fun uu____26613  ->
                       let uu____26614 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26616 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26614 uu____26616)
                   in
                giveup env uu____26606 orig)
             else
               (let uu____26621 =
                  FStar_List.fold_left2
                    (fun uu____26642  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26642 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26663 =
                                 let uu____26668 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26669 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26668
                                   FStar_TypeChecker_Common.EQ uu____26669
                                   "effect universes"
                                  in
                               (match uu____26663 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26621 with
                | (univ_sub_probs,wl1) ->
                    let uu____26689 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26689 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26697 =
                           FStar_List.fold_right2
                             (fun uu____26734  ->
                                fun uu____26735  ->
                                  fun uu____26736  ->
                                    match (uu____26734, uu____26735,
                                            uu____26736)
                                    with
                                    | ((a1,uu____26780),(a2,uu____26782),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26815 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26815 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26697 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26842 =
                                  let uu____26845 =
                                    let uu____26848 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26848
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26845
                                   in
                                FStar_List.append univ_sub_probs uu____26842
                                 in
                              let guard =
                                let guard =
                                  let uu____26870 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26870  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3527_26879 = wl3  in
                                {
                                  attempting = (uu___3527_26879.attempting);
                                  wl_deferred = (uu___3527_26879.wl_deferred);
                                  ctr = (uu___3527_26879.ctr);
                                  defer_ok = (uu___3527_26879.defer_ok);
                                  smt_ok = (uu___3527_26879.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3527_26879.umax_heuristic_ok);
                                  tcenv = (uu___3527_26879.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26881 = attempt sub_probs wl5  in
                              solve env uu____26881))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26899 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26899
           then
             let uu____26904 =
               let uu____26906 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26906
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26908 =
               let uu____26910 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26910
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26904 uu____26908
           else ());
          (let uu____26915 =
             let uu____26920 =
               let uu____26925 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26925
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26920
               (fun uu____26942  ->
                  match uu____26942 with
                  | (c,g) ->
                      let uu____26953 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26953, g))
              in
           match uu____26915 with
           | (c12,g_lift) ->
               ((let uu____26957 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26957
                 then
                   let uu____26962 =
                     let uu____26964 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26964
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26966 =
                     let uu____26968 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26968
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26962 uu____26966
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3547_26978 = wl  in
                     {
                       attempting = (uu___3547_26978.attempting);
                       wl_deferred = (uu___3547_26978.wl_deferred);
                       ctr = (uu___3547_26978.ctr);
                       defer_ok = (uu___3547_26978.defer_ok);
                       smt_ok = (uu___3547_26978.smt_ok);
                       umax_heuristic_ok =
                         (uu___3547_26978.umax_heuristic_ok);
                       tcenv = (uu___3547_26978.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26979 =
                     let rec is_uvar t =
                       let uu____26993 =
                         let uu____26994 = FStar_Syntax_Subst.compress t  in
                         uu____26994.FStar_Syntax_Syntax.n  in
                       match uu____26993 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26998 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27013) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27019) ->
                           is_uvar t1
                       | uu____27044 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27078  ->
                          fun uu____27079  ->
                            fun uu____27080  ->
                              match (uu____27078, uu____27079, uu____27080)
                              with
                              | ((a1,uu____27124),(a2,uu____27126),(is_sub_probs,wl2))
                                  ->
                                  let uu____27159 = is_uvar a1  in
                                  if uu____27159
                                  then
                                    ((let uu____27169 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27169
                                      then
                                        let uu____27174 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27176 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27174 uu____27176
                                      else ());
                                     (let uu____27181 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27181 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26979 with
                   | (is_sub_probs,wl2) ->
                       let uu____27209 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27209 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27217 =
                              let uu____27222 =
                                let uu____27223 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27223
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27222
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27217 with
                             | (uu____27230,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27241 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27243 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27241 s uu____27243
                                    in
                                 let uu____27246 =
                                   let uu____27275 =
                                     let uu____27276 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27276.FStar_Syntax_Syntax.n  in
                                   match uu____27275 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27336 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27336 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27399 =
                                              let uu____27418 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27418
                                                (fun uu____27522  ->
                                                   match uu____27522 with
                                                   | (l1,l2) ->
                                                       let uu____27595 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27595))
                                               in
                                            (match uu____27399 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27700 ->
                                       let uu____27701 =
                                         let uu____27707 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27707)
                                          in
                                       FStar_Errors.raise_error uu____27701 r
                                    in
                                 (match uu____27246 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27783 =
                                        let uu____27790 =
                                          let uu____27791 =
                                            let uu____27792 =
                                              let uu____27799 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27799,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27792
                                             in
                                          [uu____27791]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27790
                                          (fun b  ->
                                             let uu____27815 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27817 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27819 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27815 uu____27817
                                               uu____27819) r
                                         in
                                      (match uu____27783 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27829 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27829
                                             then
                                               let uu____27834 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27843 =
                                                          let uu____27845 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27845
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27843) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27834
                                             else ());
                                            (let wl4 =
                                               let uu___3619_27853 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3619_27853.attempting);
                                                 wl_deferred =
                                                   (uu___3619_27853.wl_deferred);
                                                 ctr = (uu___3619_27853.ctr);
                                                 defer_ok =
                                                   (uu___3619_27853.defer_ok);
                                                 smt_ok =
                                                   (uu___3619_27853.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3619_27853.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3619_27853.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27878 =
                                                        let uu____27885 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27885, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27878) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27902 =
                                               let f_sort_is =
                                                 let uu____27912 =
                                                   let uu____27913 =
                                                     let uu____27916 =
                                                       let uu____27917 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27917.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27916
                                                      in
                                                   uu____27913.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27912 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27928,uu____27929::is)
                                                     ->
                                                     let uu____27971 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27971
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28004 ->
                                                     let uu____28005 =
                                                       let uu____28011 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28011)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28005 r
                                                  in
                                               let uu____28017 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28052  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28052
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28073 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28073
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28017
                                                in
                                             match uu____27902 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28098 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28098
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28099 =
                                                   let g_sort_is =
                                                     let uu____28109 =
                                                       let uu____28110 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28110.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28109 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28115,uu____28116::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28176 ->
                                                         let uu____28177 =
                                                           let uu____28183 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28183)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28177 r
                                                      in
                                                   let uu____28189 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28224  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28224
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28245
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28245
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28189
                                                    in
                                                 (match uu____28099 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28272 =
                                                          let uu____28277 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28278 =
                                                            let uu____28279 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28279
                                                             in
                                                          (uu____28277,
                                                            uu____28278)
                                                           in
                                                        match uu____28272
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28307 =
                                                          let uu____28310 =
                                                            let uu____28313 =
                                                              let uu____28316
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28316
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28313
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28310
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28307
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28340 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28340
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
                                                        let uu____28351 =
                                                          let uu____28354 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28357 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28357)
                                                            uu____28354
                                                           in
                                                        solve_prob orig
                                                          uu____28351 [] wl6
                                                         in
                                                      let uu____28358 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28358))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28381 =
            let univs =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28383 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28383]
              | x -> x  in
            let c12 =
              let uu___3685_28386 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3685_28386.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3685_28386.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3685_28386.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3685_28386.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28387 =
              let uu____28392 =
                FStar_All.pipe_right
                  (let uu___3688_28394 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3688_28394.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3688_28394.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3688_28394.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3688_28394.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28392
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28387
              (fun uu____28408  ->
                 match uu____28408 with
                 | (c,g) ->
                     let uu____28415 =
                       let uu____28417 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28417  in
                     if uu____28415
                     then
                       let uu____28420 =
                         let uu____28426 =
                           let uu____28428 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28430 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28428 uu____28430
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28426)
                          in
                       FStar_Errors.raise_error uu____28420 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28436 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28436
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28442 = lift_c1 ()  in
               solve_eq uu____28442 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___28_28451  ->
                         match uu___28_28451 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28456 -> false))
                  in
               let uu____28458 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28488)::uu____28489,(wp2,uu____28491)::uu____28492)
                     -> (wp1, wp2)
                 | uu____28565 ->
                     let uu____28590 =
                       let uu____28596 =
                         let uu____28598 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28600 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28598 uu____28600
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28596)
                        in
                     FStar_Errors.raise_error uu____28590
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28458 with
               | (wpc1,wpc2) ->
                   let uu____28610 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28610
                   then
                     let uu____28613 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28613 wl
                   else
                     (let uu____28617 =
                        let uu____28624 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28624  in
                      match uu____28617 with
                      | (c2_decl,qualifiers) ->
                          let uu____28645 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28645
                          then
                            let c1_repr =
                              let uu____28652 =
                                let uu____28653 =
                                  let uu____28654 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28654  in
                                let uu____28655 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28653 uu____28655
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28652
                               in
                            let c2_repr =
                              let uu____28658 =
                                let uu____28659 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28660 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28659 uu____28660
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28658
                               in
                            let uu____28662 =
                              let uu____28667 =
                                let uu____28669 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28671 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28669
                                  uu____28671
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28667
                               in
                            (match uu____28662 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28677 = attempt [prob] wl2  in
                                 solve env uu____28677)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28697 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28697
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28720 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28720
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
                                        let uu____28730 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28730 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28737 =
                                        let uu____28744 =
                                          let uu____28745 =
                                            let uu____28762 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28765 =
                                              let uu____28776 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28776; wpc1_2]  in
                                            (uu____28762, uu____28765)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28745
                                           in
                                        FStar_Syntax_Syntax.mk uu____28744
                                         in
                                      uu____28737
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
                                     let uu____28825 =
                                       let uu____28832 =
                                         let uu____28833 =
                                           let uu____28850 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28853 =
                                             let uu____28864 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28873 =
                                               let uu____28884 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28884; wpc1_2]  in
                                             uu____28864 :: uu____28873  in
                                           (uu____28850, uu____28853)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28833
                                          in
                                       FStar_Syntax_Syntax.mk uu____28832  in
                                     uu____28825 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28938 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28938
                              then
                                let uu____28943 =
                                  let uu____28945 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28945
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28943
                              else ());
                             (let uu____28949 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28949 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28958 =
                                      let uu____28961 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____28964  ->
                                           FStar_Pervasives_Native.Some
                                             uu____28964) uu____28961
                                       in
                                    solve_prob orig uu____28958 [] wl1  in
                                  let uu____28965 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28965))))
           in
        let uu____28966 = FStar_Util.physical_equality c1 c2  in
        if uu____28966
        then
          let uu____28969 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28969
        else
          ((let uu____28973 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28973
            then
              let uu____28978 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28980 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28978
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28980
            else ());
           (let uu____28985 =
              let uu____28994 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28997 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28994, uu____28997)  in
            match uu____28985 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29015),FStar_Syntax_Syntax.Total
                    (t2,uu____29017)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29034 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29034 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29036,FStar_Syntax_Syntax.Total uu____29037) ->
                     let uu____29054 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29054 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29058),FStar_Syntax_Syntax.Total
                    (t2,uu____29060)) ->
                     let uu____29077 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29077 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29080),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29082)) ->
                     let uu____29099 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29099 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29102),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29104)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29121 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29121 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29124),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29126)) ->
                     let uu____29143 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29143 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29146,FStar_Syntax_Syntax.Comp uu____29147) ->
                     let uu____29156 =
                       let uu___3812_29159 = problem  in
                       let uu____29162 =
                         let uu____29163 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29163
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3812_29159.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29162;
                         FStar_TypeChecker_Common.relation =
                           (uu___3812_29159.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3812_29159.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3812_29159.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3812_29159.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3812_29159.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3812_29159.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3812_29159.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3812_29159.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29156 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29164,FStar_Syntax_Syntax.Comp uu____29165) ->
                     let uu____29174 =
                       let uu___3812_29177 = problem  in
                       let uu____29180 =
                         let uu____29181 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29181
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3812_29177.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29180;
                         FStar_TypeChecker_Common.relation =
                           (uu___3812_29177.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3812_29177.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3812_29177.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3812_29177.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3812_29177.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3812_29177.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3812_29177.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3812_29177.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29174 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29182,FStar_Syntax_Syntax.GTotal uu____29183) ->
                     let uu____29192 =
                       let uu___3824_29195 = problem  in
                       let uu____29198 =
                         let uu____29199 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29199
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3824_29195.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3824_29195.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3824_29195.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29198;
                         FStar_TypeChecker_Common.element =
                           (uu___3824_29195.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3824_29195.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3824_29195.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3824_29195.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3824_29195.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3824_29195.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29192 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29200,FStar_Syntax_Syntax.Total uu____29201) ->
                     let uu____29210 =
                       let uu___3824_29213 = problem  in
                       let uu____29216 =
                         let uu____29217 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29217
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3824_29213.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3824_29213.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3824_29213.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29216;
                         FStar_TypeChecker_Common.element =
                           (uu___3824_29213.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3824_29213.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3824_29213.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3824_29213.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3824_29213.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3824_29213.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29210 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29218,FStar_Syntax_Syntax.Comp uu____29219) ->
                     let uu____29220 =
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
                     if uu____29220
                     then
                       let uu____29223 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29223 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29230 =
                            let uu____29235 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29235
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29244 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29245 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29244, uu____29245))
                             in
                          match uu____29230 with
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
                           (let uu____29253 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29253
                            then
                              let uu____29258 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29260 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29258 uu____29260
                            else ());
                           (let uu____29265 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29265 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29268 =
                                  mklstr
                                    (fun uu____29275  ->
                                       let uu____29276 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29278 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29276 uu____29278)
                                   in
                                giveup env uu____29268 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29289 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29289 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29339 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29339 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29364 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29395  ->
                match uu____29395 with
                | (u1,u2) ->
                    let uu____29403 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29405 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29403 uu____29405))
         in
      FStar_All.pipe_right uu____29364 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29442,[])) when
          let uu____29469 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29469 -> "{}"
      | uu____29472 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29499 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29499
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29511 =
              FStar_List.map
                (fun uu____29524  ->
                   match uu____29524 with
                   | (uu____29531,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29511 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29542 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29542 imps
  
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
                  let uu____29599 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29599
                  then
                    let uu____29607 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29609 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29607
                      (rel_to_string rel) uu____29609
                  else "TOP"  in
                let uu____29615 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29615 with
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
              let uu____29675 =
                let uu____29678 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____29681  ->
                     FStar_Pervasives_Native.Some uu____29681) uu____29678
                 in
              FStar_Syntax_Syntax.new_bv uu____29675 t1  in
            let uu____29682 =
              let uu____29687 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29687
               in
            match uu____29682 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29745 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29745
         then
           let uu____29750 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29750
         else ());
        (let uu____29757 =
           FStar_Util.record_time (fun uu____29764  -> solve env probs)  in
         match uu____29757 with
         | (sol,ms) ->
             ((let uu____29776 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29776
               then
                 let uu____29781 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29781
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29794 =
                     FStar_Util.record_time
                       (fun uu____29801  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29794 with
                    | ((),ms1) ->
                        ((let uu____29812 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29812
                          then
                            let uu____29817 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29817
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29829 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29829
                     then
                       let uu____29836 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29836
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
          ((let uu____29862 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29862
            then
              let uu____29867 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29867
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29875 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29875
             then
               let uu____29880 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29880
             else ());
            (let f2 =
               let uu____29886 =
                 let uu____29887 = FStar_Syntax_Util.unmeta f1  in
                 uu____29887.FStar_Syntax_Syntax.n  in
               match uu____29886 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29891 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3941_29892 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3941_29892.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3941_29892.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3941_29892.FStar_TypeChecker_Common.implicits)
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
            let uu____29935 =
              let uu____29936 =
                let uu____29937 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____29938  ->
                       FStar_TypeChecker_Common.NonTrivial uu____29938)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29937;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29936  in
            FStar_All.pipe_left
              (fun uu____29945  -> FStar_Pervasives_Native.Some uu____29945)
              uu____29935
  
let with_guard_no_simp :
  'uuuuuu29955 .
    'uuuuuu29955 ->
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
            let uu____29995 =
              let uu____29996 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____29997  ->
                     FStar_TypeChecker_Common.NonTrivial uu____29997)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29996;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29995
  
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
          (let uu____30030 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30030
           then
             let uu____30035 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30037 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30035
               uu____30037
           else ());
          (let uu____30042 =
             let uu____30047 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30047
              in
           match uu____30042 with
           | (prob,wl) ->
               let g =
                 let uu____30055 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30063  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30055  in
               ((let uu____30081 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30081
                 then
                   let uu____30086 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30086
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
        let uu____30107 = try_teq true env t1 t2  in
        match uu____30107 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30112 = FStar_TypeChecker_Env.get_range env  in
              let uu____30113 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30112 uu____30113);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30121 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30121
              then
                let uu____30126 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30128 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30130 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30126
                  uu____30128 uu____30130
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
        (let uu____30154 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30154
         then
           let uu____30159 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30161 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30159
             uu____30161
         else ());
        (let uu____30166 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30166 with
         | (prob,x,wl) ->
             let g =
               let uu____30181 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30190  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30181  in
             ((let uu____30208 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30208
               then
                 let uu____30213 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30213
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30221 =
                     let uu____30222 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30222 g1  in
                   FStar_Pervasives_Native.Some uu____30221)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30244 = FStar_TypeChecker_Env.get_range env  in
          let uu____30245 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30244 uu____30245
  
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
        (let uu____30274 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30274
         then
           let uu____30279 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30281 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30279 uu____30281
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30292 =
           let uu____30299 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30299 "sub_comp"
            in
         match uu____30292 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30312 =
                 FStar_Util.record_time
                   (fun uu____30324  ->
                      let uu____30325 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30334  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30325)
                  in
               match uu____30312 with
               | (r,ms) ->
                   ((let uu____30362 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30362
                     then
                       let uu____30367 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30369 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30371 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30367 uu____30369
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30371
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
      fun uu____30409  ->
        match uu____30409 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30452 =
                 let uu____30458 =
                   let uu____30460 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30462 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30460 uu____30462
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30458)  in
               let uu____30466 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30452 uu____30466)
               in
            let equiv v v' =
              let uu____30479 =
                let uu____30484 = FStar_Syntax_Subst.compress_univ v  in
                let uu____30485 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30484, uu____30485)  in
              match uu____30479 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30505 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____30536 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____30536 with
                      | FStar_Syntax_Syntax.U_unif uu____30543 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30572  ->
                                    match uu____30572 with
                                    | (u,v') ->
                                        let uu____30581 = equiv v v'  in
                                        if uu____30581
                                        then
                                          let uu____30586 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____30586 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____30607 -> []))
               in
            let uu____30612 =
              let wl =
                let uu___4052_30616 = empty_worklist env  in
                {
                  attempting = (uu___4052_30616.attempting);
                  wl_deferred = (uu___4052_30616.wl_deferred);
                  ctr = (uu___4052_30616.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4052_30616.smt_ok);
                  umax_heuristic_ok = (uu___4052_30616.umax_heuristic_ok);
                  tcenv = (uu___4052_30616.tcenv);
                  wl_implicits = (uu___4052_30616.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30635  ->
                      match uu____30635 with
                      | (lb,v) ->
                          let uu____30642 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____30642 with
                           | USolved wl1 -> ()
                           | uu____30645 -> fail lb v)))
               in
            let rec check_ineq uu____30656 =
              match uu____30656 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30668) -> true
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
                      uu____30692,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30694,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30705) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____30713,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____30722 -> false)
               in
            let uu____30728 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30745  ->
                      match uu____30745 with
                      | (u,v) ->
                          let uu____30753 = check_ineq (u, v)  in
                          if uu____30753
                          then true
                          else
                            ((let uu____30761 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30761
                              then
                                let uu____30766 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30768 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____30766
                                  uu____30768
                              else ());
                             false)))
               in
            if uu____30728
            then ()
            else
              ((let uu____30778 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30778
                then
                  ((let uu____30784 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30784);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30796 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30796))
                else ());
               (let uu____30809 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30809))
  
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
        let fail uu____30882 =
          match uu____30882 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4129_30905 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4129_30905.attempting);
            wl_deferred = (uu___4129_30905.wl_deferred);
            ctr = (uu___4129_30905.ctr);
            defer_ok;
            smt_ok = (uu___4129_30905.smt_ok);
            umax_heuristic_ok = (uu___4129_30905.umax_heuristic_ok);
            tcenv = (uu___4129_30905.tcenv);
            wl_implicits = (uu___4129_30905.wl_implicits)
          }  in
        (let uu____30908 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30908
         then
           let uu____30913 = FStar_Util.string_of_bool defer_ok  in
           let uu____30915 = wl_to_string wl  in
           let uu____30917 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30913 uu____30915 uu____30917
         else ());
        (let g1 =
           let uu____30923 = solve_and_commit env wl fail  in
           match uu____30923 with
           | FStar_Pervasives_Native.Some
               (uu____30930::uu____30931,uu____30932) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4144_30961 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4144_30961.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4144_30961.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30962 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4149_30971 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4149_30971.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4149_30971.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4149_30971.FStar_TypeChecker_Common.implicits)
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
            let uu___4161_31048 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4161_31048.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4161_31048.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4161_31048.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31049 =
            let uu____31051 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31051  in
          if uu____31049
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug
                  then
                    (let uu____31063 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31064 =
                       let uu____31066 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31066
                        in
                     FStar_Errors.diag uu____31063 uu____31064)
                  else ();
                  (let vc1 =
                     let uu____31072 =
                       let uu____31076 =
                         let uu____31078 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31078  in
                       FStar_Pervasives_Native.Some uu____31076  in
                     FStar_Profiling.profile
                       (fun uu____31081  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31072 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug
                   then
                     (let uu____31085 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31086 =
                        let uu____31088 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31088
                         in
                      FStar_Errors.diag uu____31085 uu____31086)
                   else ();
                   (let uu____31094 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31094
                      "discharge_guard'" env vc1);
                   (let uu____31096 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31096 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug
                           then
                             (let uu____31105 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31106 =
                                let uu____31108 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31108
                                 in
                              FStar_Errors.diag uu____31105 uu____31106)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug
                           then
                             (let uu____31118 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31119 =
                                let uu____31121 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31121
                                 in
                              FStar_Errors.diag uu____31118 uu____31119)
                           else ();
                           (let vcs =
                              let uu____31135 = FStar_Options.use_tactics ()
                                 in
                              if uu____31135
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31157  ->
                                     (let uu____31159 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____31161  -> ()) uu____31159);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31204  ->
                                              match uu____31204 with
                                              | (env1,goal,opts) ->
                                                  let uu____31220 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31220, opts)))))
                              else
                                (let uu____31224 =
                                   let uu____31231 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31231)  in
                                 [uu____31224])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31264  ->
                                    match uu____31264 with
                                    | (env1,goal,opts) ->
                                        let uu____31274 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31274 with
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
                                                (let uu____31285 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31286 =
                                                   let uu____31288 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31290 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31288 uu____31290
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31285 uu____31286)
                                              else ();
                                              if debug
                                              then
                                                (let uu____31297 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31298 =
                                                   let uu____31300 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31300
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31297 uu____31298)
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
      let uu____31318 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31318 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31327 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31327
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31341 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31341 with
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
        let uu____31371 = try_teq false env t1 t2  in
        match uu____31371 with
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
            let uu____31415 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31415 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31428 ->
                     let uu____31441 =
                       let uu____31442 = FStar_Syntax_Subst.compress r  in
                       uu____31442.FStar_Syntax_Syntax.n  in
                     (match uu____31441 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31447) ->
                          unresolved ctx_u'
                      | uu____31464 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31488 = acc  in
            match uu____31488 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____31507 = hd  in
                     (match uu____31507 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____31518 = unresolved ctx_u  in
                             if uu____31518
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd :: out), changed) tl
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31542 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31542
                                     then
                                       let uu____31546 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31546
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31555 = teq_nosmt env1 t tm
                                          in
                                       match uu____31555 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4274_31565 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4274_31565.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4274_31565.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4274_31565.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4274_31565.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4274_31565.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4274_31565.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4274_31565.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4277_31573 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4277_31573.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4277_31573.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4277_31573.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4281_31584 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4281_31584.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4281_31584.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4281_31584.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4281_31584.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4281_31584.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4281_31584.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4281_31584.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4281_31584.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4281_31584.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4281_31584.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4281_31584.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4281_31584.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4281_31584.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4281_31584.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4281_31584.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4281_31584.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4281_31584.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4281_31584.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4281_31584.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4281_31584.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4281_31584.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4281_31584.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4281_31584.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4281_31584.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4281_31584.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4281_31584.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4281_31584.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4281_31584.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4281_31584.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4281_31584.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4281_31584.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4281_31584.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4281_31584.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4281_31584.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4281_31584.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4281_31584.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4281_31584.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4281_31584.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4281_31584.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4281_31584.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4281_31584.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4281_31584.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4281_31584.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4281_31584.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4281_31584.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4286_31589 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4286_31589.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4286_31589.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4286_31589.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4286_31589.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4286_31589.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4286_31589.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4286_31589.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4286_31589.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4286_31589.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4286_31589.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4286_31589.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4286_31589.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4286_31589.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4286_31589.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4286_31589.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4286_31589.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4286_31589.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4286_31589.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4286_31589.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4286_31589.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4286_31589.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4286_31589.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4286_31589.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4286_31589.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4286_31589.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4286_31589.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4286_31589.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4286_31589.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4286_31589.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4286_31589.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4286_31589.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4286_31589.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4286_31589.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4286_31589.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4286_31589.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4286_31589.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4286_31589.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31594 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31594
                                   then
                                     let uu____31599 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31601 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31603 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31605 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31599 uu____31601 uu____31603
                                       reason uu____31605
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4292_31612  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31619 =
                                             let uu____31629 =
                                               let uu____31637 =
                                                 let uu____31639 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31641 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31643 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31639 uu____31641
                                                   uu____31643
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31637, r)
                                                in
                                             [uu____31629]  in
                                           FStar_Errors.add_errors
                                             uu____31619);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31662 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31673  ->
                                               let uu____31674 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31676 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31678 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31674 uu____31676
                                                 reason uu____31678)) env2 g1
                                         true
                                        in
                                     match uu____31662 with
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
          let uu___4304_31686 = g  in
          let uu____31687 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4304_31686.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4304_31686.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4304_31686.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31687
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
        let uu____31727 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31727 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31728 = discharge_guard env g1  in
          FStar_All.pipe_left (fun uu____31729  -> ()) uu____31728
      | imp::uu____31731 ->
          let uu____31734 =
            let uu____31740 =
              let uu____31742 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31744 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31742 uu____31744
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31740)
             in
          FStar_Errors.raise_error uu____31734
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31764 = teq env t1 t2  in
        force_trivial_guard env uu____31764
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31783 = teq_nosmt env t1 t2  in
        match uu____31783 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4329_31802 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4329_31802.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4329_31802.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4329_31802.FStar_TypeChecker_Common.implicits)
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
        (let uu____31838 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31838
         then
           let uu____31843 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31845 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31843
             uu____31845
         else ());
        (let uu____31850 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31850 with
         | (prob,x,wl) ->
             let g =
               let uu____31869 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31878  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31869  in
             ((let uu____31896 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31896
               then
                 let uu____31901 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31903 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31905 =
                   let uu____31907 = FStar_Util.must g  in
                   guard_to_string env uu____31907  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31901 uu____31903 uu____31905
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
        let uu____31944 = check_subtyping env t1 t2  in
        match uu____31944 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31963 =
              let uu____31964 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31964 g  in
            FStar_Pervasives_Native.Some uu____31963
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31983 = check_subtyping env t1 t2  in
        match uu____31983 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32002 =
              let uu____32003 =
                let uu____32004 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32004]  in
              FStar_TypeChecker_Env.close_guard env uu____32003 g  in
            FStar_Pervasives_Native.Some uu____32002
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32042 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32042
         then
           let uu____32047 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32049 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32047
             uu____32049
         else ());
        (let uu____32054 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32054 with
         | (prob,x,wl) ->
             let g =
               let uu____32069 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32078  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32069  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32099 =
                      let uu____32100 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32100]  in
                    FStar_TypeChecker_Env.close_guard env uu____32099 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32141 = subtype_nosmt env t1 t2  in
        match uu____32141 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  