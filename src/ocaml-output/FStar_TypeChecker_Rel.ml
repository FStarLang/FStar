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
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____5927 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5927 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5978 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6035  ->
             match uu____6035 with
             | (x,uu____6047) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6065 = FStar_List.last bs  in
      match uu____6065 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6089) ->
          let uu____6100 =
            FStar_Util.prefix_until
              (fun uu___18_6115  ->
                 match uu___18_6115 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6118 -> false) g
             in
          (match uu____6100 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6132,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6169 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6169 with
        | (pfx,uu____6179) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6191 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6191 with
             | (uu____6199,src',wl1) ->
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
                 | uu____6313 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6314 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6378  ->
                  fun uu____6379  ->
                    match (uu____6378, uu____6379) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6482 =
                          let uu____6484 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6484
                           in
                        if uu____6482
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6518 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6518
                           then
                             let uu____6535 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6535)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6314 with | (isect,uu____6585) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu6621 'uuuuuu6622 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6621) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6622) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6680  ->
              fun uu____6681  ->
                match (uu____6680, uu____6681) with
                | ((a,uu____6700),(b,uu____6702)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu6718 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6718) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6749  ->
           match uu____6749 with
           | (y,uu____6756) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu6766 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6766) Prims.list ->
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
                   let uu____6928 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6928
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6961 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7013 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7057 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7078 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7086  ->
    match uu___19_7086 with
    | MisMatch (d1,d2) ->
        let uu____7098 =
          let uu____7100 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7102 =
            let uu____7104 =
              let uu____7106 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7106 ")"  in
            Prims.op_Hat ") (" uu____7104  in
          Prims.op_Hat uu____7100 uu____7102  in
        Prims.op_Hat "MisMatch (" uu____7098
    | HeadMatch u ->
        let uu____7113 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7113
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7122  ->
    match uu___20_7122 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7139 -> HeadMatch false
  
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
          let uu____7161 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7161 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7172 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7196 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7206 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7225 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7225
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7226 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7227 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7228 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7241 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7255 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7279) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7285,uu____7286) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7328) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7353;
             FStar_Syntax_Syntax.index = uu____7354;
             FStar_Syntax_Syntax.sort = t2;_},uu____7356)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7364 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7365 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7366 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7381 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7388 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7408 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7408
  
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
           { FStar_Syntax_Syntax.blob = uu____7427;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7428;
             FStar_Syntax_Syntax.ltyp = uu____7429;
             FStar_Syntax_Syntax.rng = uu____7430;_},uu____7431)
            ->
            let uu____7442 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7442 t21
        | (uu____7443,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7444;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7445;
             FStar_Syntax_Syntax.ltyp = uu____7446;
             FStar_Syntax_Syntax.rng = uu____7447;_})
            ->
            let uu____7458 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7458
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7470 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7470
            then FullMatch
            else
              (let uu____7475 =
                 let uu____7484 =
                   let uu____7487 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7487  in
                 let uu____7488 =
                   let uu____7491 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7491  in
                 (uu____7484, uu____7488)  in
               MisMatch uu____7475)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7497),FStar_Syntax_Syntax.Tm_uinst (g,uu____7499)) ->
            let uu____7508 = head_matches env f g  in
            FStar_All.pipe_right uu____7508 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7509) -> HeadMatch true
        | (uu____7511,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7515 = FStar_Const.eq_const c d  in
            if uu____7515
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7525),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7527)) ->
            let uu____7560 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7560
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7570),FStar_Syntax_Syntax.Tm_refine (y,uu____7572)) ->
            let uu____7581 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7581 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7583),uu____7584) ->
            let uu____7589 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7589 head_match
        | (uu____7590,FStar_Syntax_Syntax.Tm_refine (x,uu____7592)) ->
            let uu____7597 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7597 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7598,FStar_Syntax_Syntax.Tm_type
           uu____7599) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7601,FStar_Syntax_Syntax.Tm_arrow uu____7602) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____7633),FStar_Syntax_Syntax.Tm_app (head',uu____7635))
            ->
            let uu____7684 = head_matches env head head'  in
            FStar_All.pipe_right uu____7684 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____7686),uu____7687) ->
            let uu____7712 = head_matches env head t21  in
            FStar_All.pipe_right uu____7712 head_match
        | (uu____7713,FStar_Syntax_Syntax.Tm_app (head,uu____7715)) ->
            let uu____7740 = head_matches env t11 head  in
            FStar_All.pipe_right uu____7740 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7741,FStar_Syntax_Syntax.Tm_let
           uu____7742) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7770,FStar_Syntax_Syntax.Tm_match uu____7771) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7817,FStar_Syntax_Syntax.Tm_abs
           uu____7818) -> HeadMatch true
        | uu____7856 ->
            let uu____7861 =
              let uu____7870 = delta_depth_of_term env t11  in
              let uu____7873 = delta_depth_of_term env t21  in
              (uu____7870, uu____7873)  in
            MisMatch uu____7861
  
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
              let uu____7942 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7942  in
            (let uu____7944 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7944
             then
               let uu____7949 = FStar_Syntax_Print.term_to_string t  in
               let uu____7951 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7949 uu____7951
             else ());
            (let uu____7956 =
               let uu____7957 = FStar_Syntax_Util.un_uinst head  in
               uu____7957.FStar_Syntax_Syntax.n  in
             match uu____7956 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7963 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7963 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7977 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7977
                        then
                          let uu____7982 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7982
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7987 ->
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
                      let uu____8005 =
                        let uu____8007 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8007 = FStar_Syntax_Util.Equal  in
                      if uu____8005
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8014 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8014
                          then
                            let uu____8019 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8021 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8019
                              uu____8021
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8026 -> FStar_Pervasives_Native.None)
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
            (let uu____8178 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8178
             then
               let uu____8183 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8185 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8187 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8183
                 uu____8185 uu____8187
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8215 =
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
               match uu____8215 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8263 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8263 with
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
                  uu____8301),uu____8302)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8323 =
                      let uu____8332 = maybe_inline t11  in
                      let uu____8335 = maybe_inline t21  in
                      (uu____8332, uu____8335)  in
                    match uu____8323 with
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
                 (uu____8378,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8379))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8400 =
                      let uu____8409 = maybe_inline t11  in
                      let uu____8412 = maybe_inline t21  in
                      (uu____8409, uu____8412)  in
                    match uu____8400 with
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
             | MisMatch uu____8467 -> fail n_delta r t11 t21
             | uu____8476 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8491 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8491
           then
             let uu____8496 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8498 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8500 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8508 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8525 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8525
                    (fun uu____8560  ->
                       match uu____8560 with
                       | (t11,t21) ->
                           let uu____8568 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8570 =
                             let uu____8572 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8572  in
                           Prims.op_Hat uu____8568 uu____8570))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8496 uu____8498 uu____8500 uu____8508
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8589 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8589 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8604  ->
    match uu___21_8604 with
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
      let uu___1228_8653 = p  in
      let uu____8656 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8657 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1228_8653.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8656;
        FStar_TypeChecker_Common.relation =
          (uu___1228_8653.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8657;
        FStar_TypeChecker_Common.element =
          (uu___1228_8653.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1228_8653.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1228_8653.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1228_8653.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1228_8653.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1228_8653.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8672 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8672
            (fun uu____8677  -> FStar_TypeChecker_Common.TProb uu____8677)
      | FStar_TypeChecker_Common.CProb uu____8678 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8701 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8701 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8709 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8709 with
           | (lh,lhs_args) ->
               let uu____8756 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8756 with
                | (rh,rhs_args) ->
                    let uu____8803 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8816,FStar_Syntax_Syntax.Tm_uvar uu____8817)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8906 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8933,uu____8934)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8949,FStar_Syntax_Syntax.Tm_uvar uu____8950)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8965,FStar_Syntax_Syntax.Tm_arrow uu____8966)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_8996 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_8996.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_8996.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_8996.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_8996.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_8996.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_8996.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_8996.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_8996.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_8996.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8999,FStar_Syntax_Syntax.Tm_type uu____9000)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_9016 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_9016.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_9016.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_9016.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_9016.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_9016.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_9016.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_9016.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_9016.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_9016.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9019,FStar_Syntax_Syntax.Tm_uvar uu____9020)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1279_9036 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1279_9036.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1279_9036.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1279_9036.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1279_9036.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1279_9036.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1279_9036.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1279_9036.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1279_9036.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1279_9036.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9039,FStar_Syntax_Syntax.Tm_uvar uu____9040)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9055,uu____9056)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9071,FStar_Syntax_Syntax.Tm_uvar uu____9072)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9087,uu____9088) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8803 with
                     | (rank,tp1) ->
                         let uu____9101 =
                           FStar_All.pipe_right
                             (let uu___1299_9105 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1299_9105.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1299_9105.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1299_9105.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1299_9105.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1299_9105.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1299_9105.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1299_9105.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1299_9105.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1299_9105.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9108  ->
                                FStar_TypeChecker_Common.TProb uu____9108)
                            in
                         (rank, uu____9101))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9112 =
            FStar_All.pipe_right
              (let uu___1303_9116 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1303_9116.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1303_9116.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1303_9116.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1303_9116.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1303_9116.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1303_9116.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1303_9116.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1303_9116.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1303_9116.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9119  -> FStar_TypeChecker_Common.CProb uu____9119)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9112)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9179 probs =
      match uu____9179 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9260 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9281 = rank wl.tcenv hd  in
               (match uu____9281 with
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
                      (let uu____9342 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9347 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9347)
                          in
                       if uu____9342
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
          let uu____9420 = FStar_Syntax_Util.head_and_args t  in
          match uu____9420 with
          | (hd,uu____9439) ->
              let uu____9464 =
                let uu____9465 = FStar_Syntax_Subst.compress hd  in
                uu____9465.FStar_Syntax_Syntax.n  in
              (match uu____9464 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9470) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9505  ->
                           match uu____9505 with
                           | (y,uu____9514) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9537  ->
                                       match uu____9537 with
                                       | (x,uu____9546) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9551 -> false)
           in
        let uu____9553 = rank tcenv p  in
        match uu____9553 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9562 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9643 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9662 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9681 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9698 = FStar_Thunk.mkv s  in UFailed uu____9698 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9713 = mklstr s  in UFailed uu____9713 
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
                        let uu____9764 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9764 with
                        | (k,uu____9772) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9785 -> false)))
            | uu____9787 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9839 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9847 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9847 = Prims.int_zero))
                           in
                        if uu____9839 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____9868 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9876 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9876 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9868)
               in
            let uu____9880 = filter u12  in
            let uu____9883 = filter u22  in (uu____9880, uu____9883)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9918 = filter_out_common_univs us1 us2  in
                   (match uu____9918 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9978 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9978 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9981 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9998  ->
                               let uu____9999 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10001 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9999 uu____10001))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10027 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10027 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10053 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10053 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10056 ->
                   ufailed_thunk
                     (fun uu____10067  ->
                        let uu____10068 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10070 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10068 uu____10070 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10073,uu____10074) ->
              let uu____10076 =
                let uu____10078 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10080 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10078 uu____10080
                 in
              failwith uu____10076
          | (FStar_Syntax_Syntax.U_unknown ,uu____10083) ->
              let uu____10084 =
                let uu____10086 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10088 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10086 uu____10088
                 in
              failwith uu____10084
          | (uu____10091,FStar_Syntax_Syntax.U_bvar uu____10092) ->
              let uu____10094 =
                let uu____10096 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10098 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10096 uu____10098
                 in
              failwith uu____10094
          | (uu____10101,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10102 =
                let uu____10104 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10106 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10104 uu____10106
                 in
              failwith uu____10102
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10136 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10136
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10153 = occurs_univ v1 u3  in
              if uu____10153
              then
                let uu____10156 =
                  let uu____10158 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10160 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10158 uu____10160
                   in
                try_umax_components u11 u21 uu____10156
              else
                (let uu____10165 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10165)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10177 = occurs_univ v1 u3  in
              if uu____10177
              then
                let uu____10180 =
                  let uu____10182 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10184 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10182 uu____10184
                   in
                try_umax_components u11 u21 uu____10180
              else
                (let uu____10189 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10189)
          | (FStar_Syntax_Syntax.U_max uu____10190,uu____10191) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10199 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10199
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10205,FStar_Syntax_Syntax.U_max uu____10206) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10214 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10214
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10220,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10222,FStar_Syntax_Syntax.U_name uu____10223) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10225) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10227) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10229,FStar_Syntax_Syntax.U_succ uu____10230) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10232,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10339 = bc1  in
      match uu____10339 with
      | (bs1,mk_cod1) ->
          let uu____10383 = bc2  in
          (match uu____10383 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10494 = aux xs ys  in
                     (match uu____10494 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10577 =
                       let uu____10584 = mk_cod1 xs  in ([], uu____10584)  in
                     let uu____10587 =
                       let uu____10594 = mk_cod2 ys  in ([], uu____10594)  in
                     (uu____10577, uu____10587)
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
                  let uu____10663 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10663 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10666 =
                    let uu____10667 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10667 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10666
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10672 = has_type_guard t1 t2  in (uu____10672, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10673 = has_type_guard t2 t1  in (uu____10673, wl)
  
let is_flex_pat :
  'uuuuuu10683 'uuuuuu10684 'uuuuuu10685 .
    ('uuuuuu10683 * 'uuuuuu10684 * 'uuuuuu10685 Prims.list) -> Prims.bool
  =
  fun uu___22_10699  ->
    match uu___22_10699 with
    | (uu____10708,uu____10709,[]) -> true
    | uu____10713 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10746 = f  in
      match uu____10746 with
      | (uu____10753,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10754;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10755;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10758;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10759;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10760;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10761;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10831  ->
                 match uu____10831 with
                 | (y,uu____10840) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10994 =
                  let uu____11009 =
                    let uu____11012 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11012  in
                  ((FStar_List.rev pat_binders), uu____11009)  in
                FStar_Pervasives_Native.Some uu____10994
            | (uu____11045,[]) ->
                let uu____11076 =
                  let uu____11091 =
                    let uu____11094 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11094  in
                  ((FStar_List.rev pat_binders), uu____11091)  in
                FStar_Pervasives_Native.Some uu____11076
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11185 =
                  let uu____11186 = FStar_Syntax_Subst.compress a  in
                  uu____11186.FStar_Syntax_Syntax.n  in
                (match uu____11185 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11206 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11206
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1631_11236 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1631_11236.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1631_11236.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11240 =
                            let uu____11241 =
                              let uu____11248 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11248)  in
                            FStar_Syntax_Syntax.NT uu____11241  in
                          [uu____11240]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1637_11264 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1637_11264.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1637_11264.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11265 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11305 =
                  let uu____11312 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11312  in
                (match uu____11305 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11371 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11396 ->
               let uu____11397 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11397 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11693 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11693
       then
         let uu____11698 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11698
       else ());
      (let uu____11704 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11704
       then
         let uu____11709 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11709
       else ());
      (let uu____11714 = next_prob probs  in
       match uu____11714 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1664_11741 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1664_11741.wl_deferred);
               ctr = (uu___1664_11741.ctr);
               defer_ok = (uu___1664_11741.defer_ok);
               smt_ok = (uu___1664_11741.smt_ok);
               umax_heuristic_ok = (uu___1664_11741.umax_heuristic_ok);
               tcenv = (uu___1664_11741.tcenv);
               wl_implicits = (uu___1664_11741.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11750 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11750
                 then
                   let uu____11753 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____11753
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
                       (let uu____11760 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd
                            probs1
                           in
                        solve env uu____11760)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1676_11766 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1676_11766.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1676_11766.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1676_11766.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1676_11766.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1676_11766.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1676_11766.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1676_11766.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1676_11766.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1676_11766.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11791 ->
                let uu____11801 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11866  ->
                          match uu____11866 with
                          | (c,uu____11876,uu____11877) -> c < probs.ctr))
                   in
                (match uu____11801 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11925 =
                            let uu____11930 =
                              FStar_List.map
                                (fun uu____11951  ->
                                   match uu____11951 with
                                   | (uu____11967,x,y) ->
                                       let uu____11978 = FStar_Thunk.force x
                                          in
                                       (uu____11978, y)) probs.wl_deferred
                               in
                            (uu____11930, (probs.wl_implicits))  in
                          Success uu____11925
                      | uu____11982 ->
                          let uu____11992 =
                            let uu___1694_11993 = probs  in
                            let uu____11994 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12015  ->
                                      match uu____12015 with
                                      | (uu____12023,uu____12024,y) -> y))
                               in
                            {
                              attempting = uu____11994;
                              wl_deferred = rest;
                              ctr = (uu___1694_11993.ctr);
                              defer_ok = (uu___1694_11993.defer_ok);
                              smt_ok = (uu___1694_11993.smt_ok);
                              umax_heuristic_ok =
                                (uu___1694_11993.umax_heuristic_ok);
                              tcenv = (uu___1694_11993.tcenv);
                              wl_implicits = (uu___1694_11993.wl_implicits)
                            }  in
                          solve env uu____11992))))

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
            let uu____12033 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12033 with
            | USolved wl1 ->
                let uu____12035 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12035
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12038 = defer_lit "" orig wl1  in
                solve env uu____12038

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
                  let uu____12089 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12089 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12092 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12105;
                  FStar_Syntax_Syntax.vars = uu____12106;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12109;
                  FStar_Syntax_Syntax.vars = uu____12110;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12123,uu____12124) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12132,FStar_Syntax_Syntax.Tm_uinst uu____12133) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12141 -> USolved wl

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
            ((let uu____12152 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12152
              then
                let uu____12157 = prob_to_string env orig  in
                let uu____12159 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12157 uu____12159
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
               let uu____12252 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12252 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12307 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12307
                then
                  let uu____12312 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12314 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12312 uu____12314
                else ());
               (let uu____12319 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12319 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12365 = eq_prob t1 t2 wl2  in
                         (match uu____12365 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12386 ->
                         let uu____12395 = eq_prob t1 t2 wl2  in
                         (match uu____12395 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12445 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12460 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12461 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12460, uu____12461)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12466 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12467 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12466, uu____12467)
                            in
                         (match uu____12445 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12498 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12498 with
                                | (t1_hd,t1_args) ->
                                    let uu____12543 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12543 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12609 =
                                              let uu____12616 =
                                                let uu____12627 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12627 :: t1_args  in
                                              let uu____12644 =
                                                let uu____12653 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12653 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12702  ->
                                                   fun uu____12703  ->
                                                     fun uu____12704  ->
                                                       match (uu____12702,
                                                               uu____12703,
                                                               uu____12704)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12754),
                                                          (a2,uu____12756))
                                                           ->
                                                           let uu____12793 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12793
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12616
                                                uu____12644
                                               in
                                            match uu____12609 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1848_12819 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1848_12819.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1848_12819.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1848_12819.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12830 =
                                                  solve env1 wl'  in
                                                (match uu____12830 with
                                                 | Success (uu____12833,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1857_12837
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1857_12837.attempting);
                                                            wl_deferred =
                                                              (uu___1857_12837.wl_deferred);
                                                            ctr =
                                                              (uu___1857_12837.ctr);
                                                            defer_ok =
                                                              (uu___1857_12837.defer_ok);
                                                            smt_ok =
                                                              (uu___1857_12837.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1857_12837.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1857_12837.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12838 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12870 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12870 with
                                | (t1_base,p1_opt) ->
                                    let uu____12906 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12906 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13005 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13005
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
                                               let uu____13058 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13058
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
                                               let uu____13090 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13090
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
                                               let uu____13122 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13122
                                           | uu____13125 -> t_base  in
                                         let uu____13142 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13142 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13156 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13156, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13163 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13163 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13199 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13199 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13235 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13235
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
                              let uu____13259 = combine t11 t21 wl2  in
                              (match uu____13259 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13292 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13292
                                     then
                                       let uu____13297 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13297
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13339 ts1 =
               match uu____13339 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13402 = pairwise out t wl2  in
                        (match uu____13402 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13438 =
               let uu____13449 = FStar_List.hd ts  in (uu____13449, [], wl1)
                in
             let uu____13458 = FStar_List.tl ts  in
             aux uu____13438 uu____13458  in
           let uu____13465 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13465 with
           | (this_flex,this_rigid) ->
               let uu____13491 =
                 let uu____13492 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13492.FStar_Syntax_Syntax.n  in
               (match uu____13491 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13517 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13517
                    then
                      let uu____13520 = destruct_flex_t this_flex wl  in
                      (match uu____13520 with
                       | (flex,wl1) ->
                           let uu____13527 = quasi_pattern env flex  in
                           (match uu____13527 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____13546 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13546
                                  then
                                    let uu____13551 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13551
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13558 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1959_13561 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1959_13561.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1959_13561.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1959_13561.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1959_13561.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1959_13561.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1959_13561.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1959_13561.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1959_13561.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1959_13561.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13558)
                | uu____13562 ->
                    ((let uu____13564 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13564
                      then
                        let uu____13569 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13569
                      else ());
                     (let uu____13574 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13574 with
                      | (u,_args) ->
                          let uu____13617 =
                            let uu____13618 = FStar_Syntax_Subst.compress u
                               in
                            uu____13618.FStar_Syntax_Syntax.n  in
                          (match uu____13617 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____13646 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13646 with
                                 | (u',uu____13665) ->
                                     let uu____13690 =
                                       let uu____13691 = whnf env u'  in
                                       uu____13691.FStar_Syntax_Syntax.n  in
                                     (match uu____13690 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13713 -> false)
                                  in
                               let uu____13715 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13738  ->
                                         match uu___23_13738 with
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
                                              | uu____13752 -> false)
                                         | uu____13756 -> false))
                                  in
                               (match uu____13715 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13771 = whnf env this_rigid
                                         in
                                      let uu____13772 =
                                        FStar_List.collect
                                          (fun uu___24_13778  ->
                                             match uu___24_13778 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13784 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13784]
                                             | uu____13788 -> [])
                                          bounds_probs
                                         in
                                      uu____13771 :: uu____13772  in
                                    let uu____13789 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13789 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13822 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13837 =
                                               let uu____13838 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13838.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13837 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13850 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13850)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13861 -> bound  in
                                           let uu____13862 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13862)  in
                                         (match uu____13822 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13897 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13897
                                                then
                                                  let wl'1 =
                                                    let uu___2019_13903 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2019_13903.wl_deferred);
                                                      ctr =
                                                        (uu___2019_13903.ctr);
                                                      defer_ok =
                                                        (uu___2019_13903.defer_ok);
                                                      smt_ok =
                                                        (uu___2019_13903.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2019_13903.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2019_13903.tcenv);
                                                      wl_implicits =
                                                        (uu___2019_13903.wl_implicits)
                                                    }  in
                                                  let uu____13904 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13904
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13910 =
                                                  solve_t env eq_prob
                                                    (let uu___2024_13912 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2024_13912.wl_deferred);
                                                       ctr =
                                                         (uu___2024_13912.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2024_13912.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2024_13912.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2024_13912.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13910 with
                                                | Success (uu____13914,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2030_13917 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2030_13917.wl_deferred);
                                                        ctr =
                                                          (uu___2030_13917.ctr);
                                                        defer_ok =
                                                          (uu___2030_13917.defer_ok);
                                                        smt_ok =
                                                          (uu___2030_13917.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2030_13917.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2030_13917.tcenv);
                                                        wl_implicits =
                                                          (uu___2030_13917.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2033_13919 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2033_13919.attempting);
                                                        wl_deferred =
                                                          (uu___2033_13919.wl_deferred);
                                                        ctr =
                                                          (uu___2033_13919.ctr);
                                                        defer_ok =
                                                          (uu___2033_13919.defer_ok);
                                                        smt_ok =
                                                          (uu___2033_13919.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2033_13919.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2033_13919.tcenv);
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
                                                    let uu____13935 =
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
                                                    ((let uu____13947 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13947
                                                      then
                                                        let uu____13952 =
                                                          let uu____13954 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13954
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13952
                                                      else ());
                                                     (let uu____13967 =
                                                        let uu____13982 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13982)
                                                         in
                                                      match uu____13967 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14004))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14030 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14030
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
                                                                  let uu____14050
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14050))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14075 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14075
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
                                                                    let uu____14095
                                                                    =
                                                                    let uu____14100
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14100
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14095
                                                                    [] wl2
                                                                     in
                                                                  let uu____14106
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14106))))
                                                      | uu____14107 ->
                                                          let uu____14122 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14122 p)))))))
                           | uu____14129 when flip ->
                               let uu____14130 =
                                 let uu____14132 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14134 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14132 uu____14134
                                  in
                               failwith uu____14130
                           | uu____14137 ->
                               let uu____14138 =
                                 let uu____14140 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14142 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14140 uu____14142
                                  in
                               failwith uu____14138)))))

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
                      (fun uu____14178  ->
                         match uu____14178 with
                         | (x,i) ->
                             let uu____14197 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14197, i)) bs_lhs
                     in
                  let uu____14200 = lhs  in
                  match uu____14200 with
                  | (uu____14201,u_lhs,uu____14203) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14300 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14310 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14310, univ)
                             in
                          match uu____14300 with
                          | (k,univ) ->
                              let uu____14317 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14317 with
                               | (uu____14334,u,wl3) ->
                                   let uu____14337 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14337, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14363 =
                              let uu____14376 =
                                let uu____14387 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14387 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14438  ->
                                   fun uu____14439  ->
                                     match (uu____14438, uu____14439) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14540 =
                                           let uu____14547 =
                                             let uu____14550 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14550
                                              in
                                           copy_uvar u_lhs [] uu____14547 wl2
                                            in
                                         (match uu____14540 with
                                          | (uu____14579,t_a,wl3) ->
                                              let uu____14582 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14582 with
                                               | (uu____14601,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14376
                                ([], wl1)
                               in
                            (match uu____14363 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2144_14657 = ct  in
                                   let uu____14658 =
                                     let uu____14661 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14661
                                      in
                                   let uu____14676 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2144_14657.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2144_14657.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14658;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14676;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2144_14657.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2147_14694 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2147_14694.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2147_14694.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14697 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____14697 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14735 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14735 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14746 =
                                          let uu____14751 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14751)  in
                                        TERM uu____14746  in
                                      let uu____14752 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14752 with
                                       | (sub_prob,wl3) ->
                                           let uu____14766 =
                                             let uu____14767 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14767
                                              in
                                           solve env uu____14766))
                             | (x,imp)::formals2 ->
                                 let uu____14789 =
                                   let uu____14796 =
                                     let uu____14799 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14799
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14796 wl1
                                    in
                                 (match uu____14789 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14820 =
                                          let uu____14823 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14823
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14820 u_x
                                         in
                                      let uu____14824 =
                                        let uu____14827 =
                                          let uu____14830 =
                                            let uu____14831 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14831, imp)  in
                                          [uu____14830]  in
                                        FStar_List.append bs_terms
                                          uu____14827
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14824 formals2 wl2)
                              in
                           let uu____14858 = occurs_check u_lhs arrow  in
                           (match uu____14858 with
                            | (uu____14871,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14887 =
                                    mklstr
                                      (fun uu____14892  ->
                                         let uu____14893 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14893)
                                     in
                                  giveup_or_defer env orig wl uu____14887
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
              (let uu____14926 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14926
               then
                 let uu____14931 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14934 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14931 (rel_to_string (p_rel orig)) uu____14934
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15065 = rhs wl1 scope env1 subst  in
                     (match uu____15065 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15088 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15088
                            then
                              let uu____15093 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15093
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15171 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15171 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2217_15173 = hd1  in
                       let uu____15174 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2217_15173.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2217_15173.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15174
                       }  in
                     let hd21 =
                       let uu___2220_15178 = hd2  in
                       let uu____15179 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2220_15178.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2220_15178.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15179
                       }  in
                     let uu____15182 =
                       let uu____15187 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15187
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15182 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15210 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15210
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15217 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15217 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15289 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15289
                                  in
                               ((let uu____15307 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15307
                                 then
                                   let uu____15312 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15314 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15312
                                     uu____15314
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15349 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15385 = aux wl [] env [] bs1 bs2  in
               match uu____15385 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15444 = attempt sub_probs wl2  in
                   solve env1 uu____15444)

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
            let uu___2258_15464 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2258_15464.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2258_15464.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15476 = try_solve env wl'  in
          match uu____15476 with
          | Success (uu____15477,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2267_15481 = wl  in
                  {
                    attempting = (uu___2267_15481.attempting);
                    wl_deferred = (uu___2267_15481.wl_deferred);
                    ctr = (uu___2267_15481.ctr);
                    defer_ok = (uu___2267_15481.defer_ok);
                    smt_ok = (uu___2267_15481.smt_ok);
                    umax_heuristic_ok = (uu___2267_15481.umax_heuristic_ok);
                    tcenv = (uu___2267_15481.tcenv);
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
        (let uu____15490 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15490 wl)

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
              let uu____15504 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15504 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15538 = lhs1  in
              match uu____15538 with
              | (uu____15541,ctx_u,uu____15543) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15551 ->
                        let uu____15552 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15552 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15601 = quasi_pattern env1 lhs1  in
              match uu____15601 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15635) ->
                  let uu____15640 = lhs1  in
                  (match uu____15640 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15655 = occurs_check ctx_u rhs1  in
                       (match uu____15655 with
                        | (uvars,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15706 =
                                let uu____15714 =
                                  let uu____15716 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15716
                                   in
                                FStar_Util.Inl uu____15714  in
                              (uu____15706, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15744 =
                                 let uu____15746 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15746  in
                               if uu____15744
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15773 =
                                    let uu____15781 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15781  in
                                  let uu____15787 =
                                    restrict_all_uvars ctx_u uvars wl1  in
                                  (uu____15773, uu____15787)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15831 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15831 with
              | (rhs_hd,args) ->
                  let uu____15874 = FStar_Util.prefix args  in
                  (match uu____15874 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15946 = lhs1  in
                       (match uu____15946 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15950 =
                              let uu____15961 =
                                let uu____15968 =
                                  let uu____15971 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15971
                                   in
                                copy_uvar u_lhs [] uu____15968 wl1  in
                              match uu____15961 with
                              | (uu____15998,t_last_arg,wl2) ->
                                  let uu____16001 =
                                    let uu____16008 =
                                      let uu____16009 =
                                        let uu____16018 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16018]  in
                                      FStar_List.append bs_lhs uu____16009
                                       in
                                    copy_uvar u_lhs uu____16008 t_res_lhs wl2
                                     in
                                  (match uu____16001 with
                                   | (uu____16053,lhs',wl3) ->
                                       let uu____16056 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16056 with
                                        | (uu____16073,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15950 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16094 =
                                     let uu____16095 =
                                       let uu____16100 =
                                         let uu____16101 =
                                           let uu____16104 =
                                             let uu____16109 =
                                               let uu____16110 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16110]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16109
                                              in
                                           uu____16104
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16101
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16100)  in
                                     TERM uu____16095  in
                                   [uu____16094]  in
                                 let uu____16135 =
                                   let uu____16142 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16142 with
                                   | (p1,wl3) ->
                                       let uu____16162 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16162 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16135 with
                                  | (sub_probs,wl3) ->
                                      let uu____16194 =
                                        let uu____16195 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16195  in
                                      solve env1 uu____16194))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16229 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16229 with
                | (uu____16247,args) ->
                    (match args with | [] -> false | uu____16283 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16302 =
                  let uu____16303 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16303.FStar_Syntax_Syntax.n  in
                match uu____16302 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16307 -> true
                | uu____16323 -> false  in
              let uu____16325 = quasi_pattern env1 lhs1  in
              match uu____16325 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16344  ->
                         let uu____16345 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16345)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16354 = is_app rhs1  in
                  if uu____16354
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16359 = is_arrow rhs1  in
                     if uu____16359
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16372  ->
                               let uu____16373 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16373)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16377 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16377
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16383 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16383
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16388 = lhs  in
                (match uu____16388 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16392 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16392 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16410 =
                              let uu____16414 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16414
                               in
                            FStar_All.pipe_right uu____16410
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16435 = occurs_check ctx_uv rhs1  in
                          (match uu____16435 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16464 =
                                   let uu____16465 =
                                     let uu____16467 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16467
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16465
                                    in
                                 giveup_or_defer env orig wl uu____16464
                               else
                                 (let uu____16475 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16475
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars wl  in
                                    let uu____16482 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16482
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16498  ->
                                              let uu____16499 =
                                                names_to_string1 fvs2  in
                                              let uu____16501 =
                                                names_to_string1 fvs1  in
                                              let uu____16503 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16499 uu____16501
                                                uu____16503)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16515 ->
                          if wl.defer_ok
                          then
                            let uu____16519 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16519
                          else
                            (let uu____16524 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16524 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16550 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16550
                             | (FStar_Util.Inl msg,uu____16552) ->
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
                  let uu____16570 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16570
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16576 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16576
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16598 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16598
                else
                  (let uu____16603 =
                     let uu____16620 = quasi_pattern env lhs  in
                     let uu____16627 = quasi_pattern env rhs  in
                     (uu____16620, uu____16627)  in
                   match uu____16603 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16670 = lhs  in
                       (match uu____16670 with
                        | ({ FStar_Syntax_Syntax.n = uu____16671;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16673;_},u_lhs,uu____16675)
                            ->
                            let uu____16678 = rhs  in
                            (match uu____16678 with
                             | (uu____16679,u_rhs,uu____16681) ->
                                 let uu____16682 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16682
                                 then
                                   let uu____16689 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16689
                                 else
                                   (let uu____16692 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16692 with
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
                                        let uu____16724 =
                                          let uu____16731 =
                                            let uu____16734 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16734
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16731
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16724 with
                                         | (uu____16746,w,wl1) ->
                                             let w_app =
                                               let uu____16752 =
                                                 let uu____16757 =
                                                   FStar_List.map
                                                     (fun uu____16768  ->
                                                        match uu____16768
                                                        with
                                                        | (z,uu____16776) ->
                                                            let uu____16781 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16781) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16757
                                                  in
                                               uu____16752
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16783 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16783
                                               then
                                                 let uu____16788 =
                                                   let uu____16792 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16794 =
                                                     let uu____16798 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16800 =
                                                       let uu____16804 =
                                                         term_to_string w  in
                                                       let uu____16806 =
                                                         let uu____16810 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16819 =
                                                           let uu____16823 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16832 =
                                                             let uu____16836
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16836]
                                                              in
                                                           uu____16823 ::
                                                             uu____16832
                                                            in
                                                         uu____16810 ::
                                                           uu____16819
                                                          in
                                                       uu____16804 ::
                                                         uu____16806
                                                        in
                                                     uu____16798 ::
                                                       uu____16800
                                                      in
                                                   uu____16792 :: uu____16794
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16788
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16853 =
                                                     let uu____16858 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16858)  in
                                                   TERM uu____16853  in
                                                 let uu____16859 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16859
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16867 =
                                                        let uu____16872 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16872)
                                                         in
                                                      TERM uu____16867  in
                                                    [s1; s2])
                                                  in
                                               let uu____16873 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16873))))))
                   | uu____16874 ->
                       let uu____16891 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16891)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16945 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16945
            then
              let uu____16950 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16952 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16954 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16956 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16950 uu____16952 uu____16954 uu____16956
            else ());
           (let uu____16967 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16967 with
            | (head1,args1) ->
                let uu____17010 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17010 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17080 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17080 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17085 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17085)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17106 =
                         mklstr
                           (fun uu____17117  ->
                              let uu____17118 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17120 = args_to_string args1  in
                              let uu____17124 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17126 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17118 uu____17120 uu____17124
                                uu____17126)
                          in
                       giveup env1 uu____17106 orig
                     else
                       (let uu____17133 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17138 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17138 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17133
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2523_17142 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2523_17142.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2523_17142.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2523_17142.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2523_17142.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2523_17142.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2523_17142.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2523_17142.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2523_17142.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17152 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17152
                                    else solve env1 wl2))
                        else
                          (let uu____17157 = base_and_refinement env1 t1  in
                           match uu____17157 with
                           | (base1,refinement1) ->
                               let uu____17182 = base_and_refinement env1 t2
                                  in
                               (match uu____17182 with
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
                                           let uu____17347 =
                                             FStar_List.fold_right
                                               (fun uu____17387  ->
                                                  fun uu____17388  ->
                                                    match (uu____17387,
                                                            uu____17388)
                                                    with
                                                    | (((a1,uu____17440),
                                                        (a2,uu____17442)),
                                                       (probs,wl3)) ->
                                                        let uu____17491 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17491
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17347 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17534 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17534
                                                 then
                                                   let uu____17539 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17539
                                                 else ());
                                                (let uu____17545 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17545
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
                                                    (let uu____17572 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17572 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17588 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17588
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17596 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17596))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17621 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17621 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17637 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17637
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17645 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17645)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17673 =
                                           match uu____17673 with
                                           | (prob,reason) ->
                                               ((let uu____17690 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17690
                                                 then
                                                   let uu____17695 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17697 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17695 uu____17697
                                                 else ());
                                                (let uu____17703 =
                                                   let uu____17712 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17715 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17712, uu____17715)
                                                    in
                                                 match uu____17703 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17728 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17728 with
                                                      | (head1',uu____17746)
                                                          ->
                                                          let uu____17771 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17771
                                                           with
                                                           | (head2',uu____17789)
                                                               ->
                                                               let uu____17814
                                                                 =
                                                                 let uu____17819
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17820
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17819,
                                                                   uu____17820)
                                                                  in
                                                               (match uu____17814
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17822
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17822
                                                                    then
                                                                    let uu____17827
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17829
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17831
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17833
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17827
                                                                    uu____17829
                                                                    uu____17831
                                                                    uu____17833
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17838
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2611_17846
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2611_17846.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2611_17846.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2611_17846.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2611_17846.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2611_17846.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2611_17846.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2611_17846.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2611_17846.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
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
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17853
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17858 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17870 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17870 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17878 =
                                             let uu____17879 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17879.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17878 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17884 -> false  in
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
                                          | uu____17887 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17890 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2631_17926 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2631_17926.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2631_17926.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2631_17926.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2631_17926.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2631_17926.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2631_17926.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2631_17926.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2631_17926.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18002 = destruct_flex_t scrutinee wl1  in
             match uu____18002 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18013 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18013 with
                  | (xs,pat_term,uu____18029,uu____18030) ->
                      let uu____18035 =
                        FStar_List.fold_left
                          (fun uu____18058  ->
                             fun x  ->
                               match uu____18058 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18079 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18079 with
                                    | (uu____18098,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18035 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18119 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18119 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2671_18136 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2671_18136.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2671_18136.umax_heuristic_ok);
                                    tcenv = (uu___2671_18136.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18147 = solve env1 wl'  in
                                (match uu____18147 with
                                 | Success (uu____18150,imps) ->
                                     let wl'1 =
                                       let uu___2679_18153 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2679_18153.wl_deferred);
                                         ctr = (uu___2679_18153.ctr);
                                         defer_ok =
                                           (uu___2679_18153.defer_ok);
                                         smt_ok = (uu___2679_18153.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2679_18153.umax_heuristic_ok);
                                         tcenv = (uu___2679_18153.tcenv);
                                         wl_implicits =
                                           (uu___2679_18153.wl_implicits)
                                       }  in
                                     let uu____18154 = solve env1 wl'1  in
                                     (match uu____18154 with
                                      | Success (uu____18157,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2687_18161 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2687_18161.attempting);
                                                 wl_deferred =
                                                   (uu___2687_18161.wl_deferred);
                                                 ctr = (uu___2687_18161.ctr);
                                                 defer_ok =
                                                   (uu___2687_18161.defer_ok);
                                                 smt_ok =
                                                   (uu___2687_18161.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2687_18161.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2687_18161.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18162 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18168 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18191 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18191
                 then
                   let uu____18196 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18198 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18196 uu____18198
                 else ());
                (let uu____18203 =
                   let uu____18224 =
                     let uu____18233 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18233)  in
                   let uu____18240 =
                     let uu____18249 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18249)  in
                   (uu____18224, uu____18240)  in
                 match uu____18203 with
                 | ((uu____18279,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18282;
                                   FStar_Syntax_Syntax.vars = uu____18283;_}),
                    (s,t)) ->
                     let uu____18354 =
                       let uu____18356 = is_flex scrutinee  in
                       Prims.op_Negation uu____18356  in
                     if uu____18354
                     then
                       ((let uu____18367 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18367
                         then
                           let uu____18372 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18372
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18391 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18391
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18406 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18406
                           then
                             let uu____18411 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18413 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18411 uu____18413
                           else ());
                          (let pat_discriminates uu___25_18438 =
                             match uu___25_18438 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18454;
                                  FStar_Syntax_Syntax.p = uu____18455;_},FStar_Pervasives_Native.None
                                ,uu____18456) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18470;
                                  FStar_Syntax_Syntax.p = uu____18471;_},FStar_Pervasives_Native.None
                                ,uu____18472) -> true
                             | uu____18499 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18602 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18602 with
                                       | (uu____18604,uu____18605,t') ->
                                           let uu____18623 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18623 with
                                            | (FullMatch ,uu____18635) ->
                                                true
                                            | (HeadMatch
                                               uu____18649,uu____18650) ->
                                                true
                                            | uu____18665 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18702 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18702
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18713 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18713 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18801,uu____18802) ->
                                       branches1
                                   | uu____18947 -> branches  in
                                 let uu____19002 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19011 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19011 with
                                        | (p,uu____19015,uu____19016) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19045  ->
                                      FStar_Util.Inr uu____19045) uu____19002))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19075 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19075 with
                                | (p,uu____19084,e) ->
                                    ((let uu____19103 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19103
                                      then
                                        let uu____19108 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19110 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19108 uu____19110
                                      else ());
                                     (let uu____19115 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19130  ->
                                           FStar_Util.Inr uu____19130)
                                        uu____19115)))))
                 | ((s,t),(uu____19133,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19136;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19137;_}))
                     ->
                     let uu____19206 =
                       let uu____19208 = is_flex scrutinee  in
                       Prims.op_Negation uu____19208  in
                     if uu____19206
                     then
                       ((let uu____19219 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19219
                         then
                           let uu____19224 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19224
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19243 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19243
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19258 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19258
                           then
                             let uu____19263 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19265 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19263 uu____19265
                           else ());
                          (let pat_discriminates uu___25_19290 =
                             match uu___25_19290 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19306;
                                  FStar_Syntax_Syntax.p = uu____19307;_},FStar_Pervasives_Native.None
                                ,uu____19308) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19322;
                                  FStar_Syntax_Syntax.p = uu____19323;_},FStar_Pervasives_Native.None
                                ,uu____19324) -> true
                             | uu____19351 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19454 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19454 with
                                       | (uu____19456,uu____19457,t') ->
                                           let uu____19475 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19475 with
                                            | (FullMatch ,uu____19487) ->
                                                true
                                            | (HeadMatch
                                               uu____19501,uu____19502) ->
                                                true
                                            | uu____19517 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19554 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19554
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19565 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19565 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19653,uu____19654) ->
                                       branches1
                                   | uu____19799 -> branches  in
                                 let uu____19854 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19863 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19863 with
                                        | (p,uu____19867,uu____19868) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19897  ->
                                      FStar_Util.Inr uu____19897) uu____19854))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19927 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19927 with
                                | (p,uu____19936,e) ->
                                    ((let uu____19955 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19955
                                      then
                                        let uu____19960 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19962 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19960 uu____19962
                                      else ());
                                     (let uu____19967 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19982  ->
                                           FStar_Util.Inr uu____19982)
                                        uu____19967)))))
                 | uu____19983 ->
                     ((let uu____20005 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20005
                       then
                         let uu____20010 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20012 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20010 uu____20012
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20058 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20058
            then
              let uu____20063 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20065 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20067 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20069 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20063 uu____20065 uu____20067 uu____20069
            else ());
           (let uu____20074 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20074 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20105,uu____20106) ->
                     let rec may_relate head =
                       let uu____20134 =
                         let uu____20135 = FStar_Syntax_Subst.compress head
                            in
                         uu____20135.FStar_Syntax_Syntax.n  in
                       match uu____20134 with
                       | FStar_Syntax_Syntax.Tm_name uu____20139 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20141 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20166 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20166 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20168 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20171
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20172 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20175,uu____20176) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20218) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20224) ->
                           may_relate t
                       | uu____20229 -> false  in
                     let uu____20231 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20231 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20244 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20244
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20254 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20254
                          then
                            let uu____20257 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20257 with
                             | (guard,wl2) ->
                                 let uu____20264 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20264)
                          else
                            (let uu____20267 =
                               mklstr
                                 (fun uu____20278  ->
                                    let uu____20279 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20281 =
                                      let uu____20283 =
                                        let uu____20287 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20287
                                          (fun x  ->
                                             let uu____20294 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20294)
                                         in
                                      FStar_Util.dflt "" uu____20283  in
                                    let uu____20299 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20301 =
                                      let uu____20303 =
                                        let uu____20307 =
                                          delta_depth_of_term env1 head2  in
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
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20279 uu____20281 uu____20299
                                      uu____20301)
                                in
                             giveup env1 uu____20267 orig))
                 | (HeadMatch (true ),uu____20320) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20335 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20335 with
                        | (guard,wl2) ->
                            let uu____20342 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20342)
                     else
                       (let uu____20345 =
                          mklstr
                            (fun uu____20352  ->
                               let uu____20353 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20355 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20353 uu____20355)
                           in
                        giveup env1 uu____20345 orig)
                 | (uu____20358,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2862_20372 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2862_20372.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2862_20372.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2862_20372.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2862_20372.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2862_20372.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2862_20372.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2862_20372.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2862_20372.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20399 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20399
          then
            let uu____20402 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20402
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20408 =
                let uu____20411 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20411  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20408 t1);
             (let uu____20430 =
                let uu____20433 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20433  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20430 t2);
             (let uu____20452 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20452
              then
                let uu____20456 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20458 =
                  let uu____20460 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20462 =
                    let uu____20464 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20464  in
                  Prims.op_Hat uu____20460 uu____20462  in
                let uu____20467 =
                  let uu____20469 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20471 =
                    let uu____20473 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20473  in
                  Prims.op_Hat uu____20469 uu____20471  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20456 uu____20458 uu____20467
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20480,uu____20481) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20497,FStar_Syntax_Syntax.Tm_delayed uu____20498) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20514,uu____20515) ->
                  let uu____20542 =
                    let uu___2893_20543 = problem  in
                    let uu____20544 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2893_20543.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20544;
                      FStar_TypeChecker_Common.relation =
                        (uu___2893_20543.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2893_20543.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2893_20543.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2893_20543.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2893_20543.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2893_20543.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2893_20543.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2893_20543.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20542 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20545,uu____20546) ->
                  let uu____20553 =
                    let uu___2899_20554 = problem  in
                    let uu____20555 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2899_20554.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20555;
                      FStar_TypeChecker_Common.relation =
                        (uu___2899_20554.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2899_20554.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2899_20554.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2899_20554.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2899_20554.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2899_20554.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2899_20554.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2899_20554.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20553 wl
              | (uu____20556,FStar_Syntax_Syntax.Tm_ascribed uu____20557) ->
                  let uu____20584 =
                    let uu___2905_20585 = problem  in
                    let uu____20586 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2905_20585.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2905_20585.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2905_20585.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20586;
                      FStar_TypeChecker_Common.element =
                        (uu___2905_20585.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2905_20585.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2905_20585.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2905_20585.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2905_20585.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2905_20585.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20584 wl
              | (uu____20587,FStar_Syntax_Syntax.Tm_meta uu____20588) ->
                  let uu____20595 =
                    let uu___2911_20596 = problem  in
                    let uu____20597 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2911_20596.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2911_20596.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2911_20596.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20597;
                      FStar_TypeChecker_Common.element =
                        (uu___2911_20596.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2911_20596.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2911_20596.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2911_20596.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2911_20596.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2911_20596.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20595 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20599),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20601)) ->
                  let uu____20610 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20610
              | (FStar_Syntax_Syntax.Tm_bvar uu____20611,uu____20612) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20614,FStar_Syntax_Syntax.Tm_bvar uu____20615) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___26_20685 =
                    match uu___26_20685 with
                    | [] -> c
                    | bs ->
                        let uu____20713 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20713
                     in
                  let uu____20724 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20724 with
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
                                    let uu____20873 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20873
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
                  let mk_t t l uu___27_20962 =
                    match uu___27_20962 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21004 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21004 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21149 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21150 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21149
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21150 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21152,uu____21153) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21184 -> true
                    | uu____21204 -> false  in
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
                      (let uu____21264 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3013_21272 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3013_21272.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3013_21272.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3013_21272.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3013_21272.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3013_21272.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3013_21272.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3013_21272.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3013_21272.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3013_21272.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3013_21272.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3013_21272.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3013_21272.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3013_21272.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3013_21272.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3013_21272.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3013_21272.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3013_21272.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3013_21272.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3013_21272.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3013_21272.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3013_21272.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3013_21272.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3013_21272.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3013_21272.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3013_21272.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3013_21272.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3013_21272.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3013_21272.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3013_21272.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3013_21272.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3013_21272.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3013_21272.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3013_21272.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3013_21272.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3013_21272.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3013_21272.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3013_21272.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3013_21272.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3013_21272.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3013_21272.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3013_21272.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3013_21272.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3013_21272.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21264 with
                       | (uu____21277,ty,uu____21279) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21288 =
                                 let uu____21289 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21289.FStar_Syntax_Syntax.n  in
                               match uu____21288 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21292 ->
                                   let uu____21299 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21299
                               | uu____21300 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21303 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21303
                             then
                               let uu____21308 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21310 =
                                 let uu____21312 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21312
                                  in
                               let uu____21313 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21308 uu____21310 uu____21313
                             else ());
                            r1))
                     in
                  let uu____21318 =
                    let uu____21335 = maybe_eta t1  in
                    let uu____21342 = maybe_eta t2  in
                    (uu____21335, uu____21342)  in
                  (match uu____21318 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3034_21384 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3034_21384.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3034_21384.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3034_21384.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3034_21384.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3034_21384.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3034_21384.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3034_21384.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3034_21384.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21405 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21405
                       then
                         let uu____21408 = destruct_flex_t not_abs wl  in
                         (match uu____21408 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21425 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21425.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21425.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21425.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21425.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21425.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21425.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21425.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21425.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21428 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21428 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21451 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21451
                       then
                         let uu____21454 = destruct_flex_t not_abs wl  in
                         (match uu____21454 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21471 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21471.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21471.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21471.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21471.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21471.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21471.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21471.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21471.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21474 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21474 orig))
                   | uu____21477 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21495,FStar_Syntax_Syntax.Tm_abs uu____21496) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21527 -> true
                    | uu____21547 -> false  in
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
                      (let uu____21607 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3013_21615 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3013_21615.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3013_21615.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3013_21615.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3013_21615.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3013_21615.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3013_21615.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3013_21615.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3013_21615.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3013_21615.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3013_21615.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3013_21615.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3013_21615.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3013_21615.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3013_21615.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3013_21615.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3013_21615.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3013_21615.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3013_21615.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3013_21615.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3013_21615.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3013_21615.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3013_21615.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3013_21615.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3013_21615.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3013_21615.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3013_21615.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3013_21615.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3013_21615.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3013_21615.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3013_21615.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3013_21615.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3013_21615.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3013_21615.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3013_21615.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3013_21615.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3013_21615.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3013_21615.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3013_21615.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3013_21615.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3013_21615.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3013_21615.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3013_21615.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3013_21615.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21607 with
                       | (uu____21620,ty,uu____21622) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21631 =
                                 let uu____21632 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21632.FStar_Syntax_Syntax.n  in
                               match uu____21631 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21635 ->
                                   let uu____21642 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21642
                               | uu____21643 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21646 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21646
                             then
                               let uu____21651 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21653 =
                                 let uu____21655 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21655
                                  in
                               let uu____21656 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21651 uu____21653 uu____21656
                             else ());
                            r1))
                     in
                  let uu____21661 =
                    let uu____21678 = maybe_eta t1  in
                    let uu____21685 = maybe_eta t2  in
                    (uu____21678, uu____21685)  in
                  (match uu____21661 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3034_21727 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3034_21727.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3034_21727.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3034_21727.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3034_21727.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3034_21727.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3034_21727.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3034_21727.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3034_21727.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21748 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21748
                       then
                         let uu____21751 = destruct_flex_t not_abs wl  in
                         (match uu____21751 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21768 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21768.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21768.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21768.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21768.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21768.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21768.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21768.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21768.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21771 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21771 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21794 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21794
                       then
                         let uu____21797 = destruct_flex_t not_abs wl  in
                         (match uu____21797 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3051_21814 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3051_21814.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3051_21814.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3051_21814.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3051_21814.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3051_21814.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3051_21814.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3051_21814.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3051_21814.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21817 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21817 orig))
                   | uu____21820 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21850 =
                    let uu____21855 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21855 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3074_21883 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3074_21883.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3074_21883.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3076_21885 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3076_21885.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3076_21885.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21886,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3074_21901 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3074_21901.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3074_21901.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3076_21903 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3076_21903.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3076_21903.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21904 -> (x1, x2)  in
                  (match uu____21850 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21923 = as_refinement false env t11  in
                       (match uu____21923 with
                        | (x12,phi11) ->
                            let uu____21931 = as_refinement false env t21  in
                            (match uu____21931 with
                             | (x22,phi21) ->
                                 ((let uu____21940 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21940
                                   then
                                     ((let uu____21945 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21947 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21949 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21945
                                         uu____21947 uu____21949);
                                      (let uu____21952 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21954 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21956 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21952
                                         uu____21954 uu____21956))
                                   else ());
                                  (let uu____21961 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21961 with
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
                                         let uu____22032 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22032
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22044 =
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
                                         (let uu____22057 =
                                            let uu____22060 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22060
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22057
                                            (p_guard base_prob));
                                         (let uu____22079 =
                                            let uu____22082 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22082
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22079
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22101 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22101)
                                          in
                                       let has_uvars =
                                         (let uu____22106 =
                                            let uu____22108 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22108
                                             in
                                          Prims.op_Negation uu____22106) ||
                                           (let uu____22112 =
                                              let uu____22114 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22114
                                               in
                                            Prims.op_Negation uu____22112)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22118 =
                                           let uu____22123 =
                                             let uu____22132 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22132]  in
                                           mk_t_problem wl1 uu____22123 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22118 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22155 =
                                                solve env1
                                                  (let uu___3119_22157 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3119_22157.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3119_22157.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3119_22157.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3119_22157.tcenv);
                                                     wl_implicits =
                                                       (uu___3119_22157.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22155 with
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
                                               | Success uu____22172 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22181 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22181
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3132_22190 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3132_22190.attempting);
                                                         wl_deferred =
                                                           (uu___3132_22190.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3132_22190.defer_ok);
                                                         smt_ok =
                                                           (uu___3132_22190.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3132_22190.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3132_22190.tcenv);
                                                         wl_implicits =
                                                           (uu___3132_22190.wl_implicits)
                                                       }  in
                                                     let uu____22192 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22192))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22195,FStar_Syntax_Syntax.Tm_uvar uu____22196) ->
                  let uu____22221 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22221 with
                   | (t11,wl1) ->
                       let uu____22228 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22228 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22237;
                    FStar_Syntax_Syntax.pos = uu____22238;
                    FStar_Syntax_Syntax.vars = uu____22239;_},uu____22240),FStar_Syntax_Syntax.Tm_uvar
                 uu____22241) ->
                  let uu____22290 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22290 with
                   | (t11,wl1) ->
                       let uu____22297 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22297 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22306,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22307;
                    FStar_Syntax_Syntax.pos = uu____22308;
                    FStar_Syntax_Syntax.vars = uu____22309;_},uu____22310))
                  ->
                  let uu____22359 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22359 with
                   | (t11,wl1) ->
                       let uu____22366 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22366 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22375;
                    FStar_Syntax_Syntax.pos = uu____22376;
                    FStar_Syntax_Syntax.vars = uu____22377;_},uu____22378),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22379;
                    FStar_Syntax_Syntax.pos = uu____22380;
                    FStar_Syntax_Syntax.vars = uu____22381;_},uu____22382))
                  ->
                  let uu____22455 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22455 with
                   | (t11,wl1) ->
                       let uu____22462 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22462 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22471,uu____22472) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22485 = destruct_flex_t t1 wl  in
                  (match uu____22485 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22492;
                    FStar_Syntax_Syntax.pos = uu____22493;
                    FStar_Syntax_Syntax.vars = uu____22494;_},uu____22495),uu____22496)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22533 = destruct_flex_t t1 wl  in
                  (match uu____22533 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22540,FStar_Syntax_Syntax.Tm_uvar uu____22541) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22554,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22555;
                    FStar_Syntax_Syntax.pos = uu____22556;
                    FStar_Syntax_Syntax.vars = uu____22557;_},uu____22558))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22595,FStar_Syntax_Syntax.Tm_arrow uu____22596) ->
                  solve_t' env
                    (let uu___3234_22624 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3234_22624.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3234_22624.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3234_22624.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3234_22624.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3234_22624.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3234_22624.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3234_22624.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3234_22624.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3234_22624.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22625;
                    FStar_Syntax_Syntax.pos = uu____22626;
                    FStar_Syntax_Syntax.vars = uu____22627;_},uu____22628),FStar_Syntax_Syntax.Tm_arrow
                 uu____22629) ->
                  solve_t' env
                    (let uu___3234_22681 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3234_22681.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3234_22681.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3234_22681.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3234_22681.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3234_22681.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3234_22681.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3234_22681.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3234_22681.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3234_22681.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22682,FStar_Syntax_Syntax.Tm_uvar uu____22683) ->
                  let uu____22696 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22696
              | (uu____22697,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22698;
                    FStar_Syntax_Syntax.pos = uu____22699;
                    FStar_Syntax_Syntax.vars = uu____22700;_},uu____22701))
                  ->
                  let uu____22738 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22738
              | (FStar_Syntax_Syntax.Tm_uvar uu____22739,uu____22740) ->
                  let uu____22753 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22753
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22754;
                    FStar_Syntax_Syntax.pos = uu____22755;
                    FStar_Syntax_Syntax.vars = uu____22756;_},uu____22757),uu____22758)
                  ->
                  let uu____22795 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22795
              | (FStar_Syntax_Syntax.Tm_refine uu____22796,uu____22797) ->
                  let t21 =
                    let uu____22805 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22805  in
                  solve_t env
                    (let uu___3269_22831 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3269_22831.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3269_22831.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3269_22831.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3269_22831.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3269_22831.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3269_22831.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3269_22831.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3269_22831.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3269_22831.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22832,FStar_Syntax_Syntax.Tm_refine uu____22833) ->
                  let t11 =
                    let uu____22841 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22841  in
                  solve_t env
                    (let uu___3276_22867 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3276_22867.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3276_22867.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3276_22867.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3276_22867.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3276_22867.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3276_22867.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3276_22867.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3276_22867.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3276_22867.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22949 =
                    let uu____22950 = guard_of_prob env wl problem t1 t2  in
                    match uu____22950 with
                    | (guard,wl1) ->
                        let uu____22957 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22957
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23176 = br1  in
                        (match uu____23176 with
                         | (p1,w1,uu____23205) ->
                             let uu____23222 = br2  in
                             (match uu____23222 with
                              | (p2,w2,uu____23245) ->
                                  let uu____23250 =
                                    let uu____23252 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23252  in
                                  if uu____23250
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23279 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23279 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23316 = br2  in
                                         (match uu____23316 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23349 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23349
                                                 in
                                              let uu____23354 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23385,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23406) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23465 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23465 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23354
                                                (fun uu____23537  ->
                                                   match uu____23537 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23574 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23574
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23595
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23595
                                                              then
                                                                let uu____23600
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23602
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23600
                                                                  uu____23602
                                                              else ());
                                                             (let uu____23608
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23608
                                                                (fun
                                                                   uu____23644
                                                                    ->
                                                                   match uu____23644
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
                    | uu____23773 -> FStar_Pervasives_Native.None  in
                  let uu____23814 = solve_branches wl brs1 brs2  in
                  (match uu____23814 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23840 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23840 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23867 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23867 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23901 =
                                FStar_List.map
                                  (fun uu____23913  ->
                                     match uu____23913 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23901  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23922 =
                              let uu____23923 =
                                let uu____23924 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23924
                                  (let uu___3375_23932 = wl3  in
                                   {
                                     attempting =
                                       (uu___3375_23932.attempting);
                                     wl_deferred =
                                       (uu___3375_23932.wl_deferred);
                                     ctr = (uu___3375_23932.ctr);
                                     defer_ok = (uu___3375_23932.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3375_23932.umax_heuristic_ok);
                                     tcenv = (uu___3375_23932.tcenv);
                                     wl_implicits =
                                       (uu___3375_23932.wl_implicits)
                                   })
                                 in
                              solve env uu____23923  in
                            (match uu____23922 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23937 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23946 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23946 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23949,uu____23950) ->
                  let head1 =
                    let uu____23974 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23974
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24020 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24020
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24066 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24066
                    then
                      let uu____24070 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24072 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24074 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24070 uu____24072 uu____24074
                    else ());
                   (let no_free_uvars t =
                      (let uu____24088 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24088) &&
                        (let uu____24092 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24092)
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
                      let uu____24111 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24111 = FStar_Syntax_Util.Equal  in
                    let uu____24112 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24112
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24116 = equal t1 t2  in
                         (if uu____24116
                          then
                            let uu____24119 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24119
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24124 =
                            let uu____24131 = equal t1 t2  in
                            if uu____24131
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24144 = mk_eq2 wl env orig t1 t2  in
                               match uu____24144 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24124 with
                          | (guard,wl1) ->
                              let uu____24165 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24165))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24168,uu____24169) ->
                  let head1 =
                    let uu____24177 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24177
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24223 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24223
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24269 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24269
                    then
                      let uu____24273 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24275 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24277 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24273 uu____24275 uu____24277
                    else ());
                   (let no_free_uvars t =
                      (let uu____24291 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24291) &&
                        (let uu____24295 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24295)
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
                      let uu____24314 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24314 = FStar_Syntax_Util.Equal  in
                    let uu____24315 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24315
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24319 = equal t1 t2  in
                         (if uu____24319
                          then
                            let uu____24322 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24322
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24327 =
                            let uu____24334 = equal t1 t2  in
                            if uu____24334
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24347 = mk_eq2 wl env orig t1 t2  in
                               match uu____24347 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24327 with
                          | (guard,wl1) ->
                              let uu____24368 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24368))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24371,uu____24372) ->
                  let head1 =
                    let uu____24374 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24374
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24420 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24420
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24466 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24466
                    then
                      let uu____24470 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24472 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24474 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24470 uu____24472 uu____24474
                    else ());
                   (let no_free_uvars t =
                      (let uu____24488 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24488) &&
                        (let uu____24492 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24492)
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
                      let uu____24511 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24511 = FStar_Syntax_Util.Equal  in
                    let uu____24512 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24512
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24516 = equal t1 t2  in
                         (if uu____24516
                          then
                            let uu____24519 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24519
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24524 =
                            let uu____24531 = equal t1 t2  in
                            if uu____24531
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24544 = mk_eq2 wl env orig t1 t2  in
                               match uu____24544 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24524 with
                          | (guard,wl1) ->
                              let uu____24565 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24565))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24568,uu____24569) ->
                  let head1 =
                    let uu____24571 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24571
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24617 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24617
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24663 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24663
                    then
                      let uu____24667 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24669 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24671 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24667 uu____24669 uu____24671
                    else ());
                   (let no_free_uvars t =
                      (let uu____24685 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24685) &&
                        (let uu____24689 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24689)
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
                      let uu____24708 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24708 = FStar_Syntax_Util.Equal  in
                    let uu____24709 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24709
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24713 = equal t1 t2  in
                         (if uu____24713
                          then
                            let uu____24716 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24716
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24721 =
                            let uu____24728 = equal t1 t2  in
                            if uu____24728
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24741 = mk_eq2 wl env orig t1 t2  in
                               match uu____24741 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24721 with
                          | (guard,wl1) ->
                              let uu____24762 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24762))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24765,uu____24766) ->
                  let head1 =
                    let uu____24768 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24768
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24814 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24814
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24860 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24860
                    then
                      let uu____24864 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24866 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24868 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24864 uu____24866 uu____24868
                    else ());
                   (let no_free_uvars t =
                      (let uu____24882 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24882) &&
                        (let uu____24886 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24886)
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
                      let uu____24905 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24905 = FStar_Syntax_Util.Equal  in
                    let uu____24906 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24906
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24910 = equal t1 t2  in
                         (if uu____24910
                          then
                            let uu____24913 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24913
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24918 =
                            let uu____24925 = equal t1 t2  in
                            if uu____24925
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24938 = mk_eq2 wl env orig t1 t2  in
                               match uu____24938 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24918 with
                          | (guard,wl1) ->
                              let uu____24959 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24959))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24962,uu____24963) ->
                  let head1 =
                    let uu____24981 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24981
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25027 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25027
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25073 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25073
                    then
                      let uu____25077 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25079 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25081 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25077 uu____25079 uu____25081
                    else ());
                   (let no_free_uvars t =
                      (let uu____25095 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25095) &&
                        (let uu____25099 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25099)
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
                      let uu____25118 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25118 = FStar_Syntax_Util.Equal  in
                    let uu____25119 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25119
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25123 = equal t1 t2  in
                         (if uu____25123
                          then
                            let uu____25126 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25126
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25131 =
                            let uu____25138 = equal t1 t2  in
                            if uu____25138
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25151 = mk_eq2 wl env orig t1 t2  in
                               match uu____25151 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25131 with
                          | (guard,wl1) ->
                              let uu____25172 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25172))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25175,FStar_Syntax_Syntax.Tm_match uu____25176) ->
                  let head1 =
                    let uu____25200 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25200
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25246 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25246
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25292 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25292
                    then
                      let uu____25296 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25298 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25300 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25296 uu____25298 uu____25300
                    else ());
                   (let no_free_uvars t =
                      (let uu____25314 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25314) &&
                        (let uu____25318 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25318)
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
                      let uu____25337 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25337 = FStar_Syntax_Util.Equal  in
                    let uu____25338 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25338
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25342 = equal t1 t2  in
                         (if uu____25342
                          then
                            let uu____25345 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25345
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25350 =
                            let uu____25357 = equal t1 t2  in
                            if uu____25357
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25370 = mk_eq2 wl env orig t1 t2  in
                               match uu____25370 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25350 with
                          | (guard,wl1) ->
                              let uu____25391 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25391))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25394,FStar_Syntax_Syntax.Tm_uinst uu____25395) ->
                  let head1 =
                    let uu____25403 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25403
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25449 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25449
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25495 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25495
                    then
                      let uu____25499 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25501 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25503 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25499 uu____25501 uu____25503
                    else ());
                   (let no_free_uvars t =
                      (let uu____25517 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25517) &&
                        (let uu____25521 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25521)
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
                      let uu____25540 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25540 = FStar_Syntax_Util.Equal  in
                    let uu____25541 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25541
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25545 = equal t1 t2  in
                         (if uu____25545
                          then
                            let uu____25548 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25548
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25553 =
                            let uu____25560 = equal t1 t2  in
                            if uu____25560
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25573 = mk_eq2 wl env orig t1 t2  in
                               match uu____25573 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25553 with
                          | (guard,wl1) ->
                              let uu____25594 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25594))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25597,FStar_Syntax_Syntax.Tm_name uu____25598) ->
                  let head1 =
                    let uu____25600 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25600
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25646 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25646
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25686 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25686
                    then
                      let uu____25690 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25692 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25694 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25690 uu____25692 uu____25694
                    else ());
                   (let no_free_uvars t =
                      (let uu____25708 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25708) &&
                        (let uu____25712 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25712)
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
                      let uu____25731 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25731 = FStar_Syntax_Util.Equal  in
                    let uu____25732 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25732
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25736 = equal t1 t2  in
                         (if uu____25736
                          then
                            let uu____25739 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25739
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25744 =
                            let uu____25751 = equal t1 t2  in
                            if uu____25751
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25764 = mk_eq2 wl env orig t1 t2  in
                               match uu____25764 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25744 with
                          | (guard,wl1) ->
                              let uu____25785 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25785))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25788,FStar_Syntax_Syntax.Tm_constant uu____25789) ->
                  let head1 =
                    let uu____25791 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25791
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25831 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25831
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25871 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25871
                    then
                      let uu____25875 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25877 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25879 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25875 uu____25877 uu____25879
                    else ());
                   (let no_free_uvars t =
                      (let uu____25893 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25893) &&
                        (let uu____25897 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25897)
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
                      let uu____25916 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25916 = FStar_Syntax_Util.Equal  in
                    let uu____25917 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25917
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25921 = equal t1 t2  in
                         (if uu____25921
                          then
                            let uu____25924 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25924
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25929 =
                            let uu____25936 = equal t1 t2  in
                            if uu____25936
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25949 = mk_eq2 wl env orig t1 t2  in
                               match uu____25949 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25929 with
                          | (guard,wl1) ->
                              let uu____25970 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25970))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25973,FStar_Syntax_Syntax.Tm_fvar uu____25974) ->
                  let head1 =
                    let uu____25976 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25976
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26022 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26022
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26068 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26068
                    then
                      let uu____26072 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26074 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26076 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26072 uu____26074 uu____26076
                    else ());
                   (let no_free_uvars t =
                      (let uu____26090 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26090) &&
                        (let uu____26094 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26094)
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
                      let uu____26113 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26113 = FStar_Syntax_Util.Equal  in
                    let uu____26114 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26114
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26118 = equal t1 t2  in
                         (if uu____26118
                          then
                            let uu____26121 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26121
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26126 =
                            let uu____26133 = equal t1 t2  in
                            if uu____26133
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26146 = mk_eq2 wl env orig t1 t2  in
                               match uu____26146 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26126 with
                          | (guard,wl1) ->
                              let uu____26167 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26167))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26170,FStar_Syntax_Syntax.Tm_app uu____26171) ->
                  let head1 =
                    let uu____26189 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26189
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26229 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26229
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26269 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26269
                    then
                      let uu____26273 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26275 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26277 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26273 uu____26275 uu____26277
                    else ());
                   (let no_free_uvars t =
                      (let uu____26291 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26291) &&
                        (let uu____26295 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26295)
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
                      let uu____26314 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26314 = FStar_Syntax_Util.Equal  in
                    let uu____26315 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26315
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26319 = equal t1 t2  in
                         (if uu____26319
                          then
                            let uu____26322 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26322
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26327 =
                            let uu____26334 = equal t1 t2  in
                            if uu____26334
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26347 = mk_eq2 wl env orig t1 t2  in
                               match uu____26347 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26327 with
                          | (guard,wl1) ->
                              let uu____26368 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26368))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26371,FStar_Syntax_Syntax.Tm_let uu____26372) ->
                  let uu____26399 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26399
                  then
                    let uu____26402 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26402
                  else
                    (let uu____26405 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26405 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26408,uu____26409) ->
                  let uu____26423 =
                    let uu____26429 =
                      let uu____26431 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26433 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26435 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26437 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26431 uu____26433 uu____26435 uu____26437
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26429)
                     in
                  FStar_Errors.raise_error uu____26423
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26441,FStar_Syntax_Syntax.Tm_let uu____26442) ->
                  let uu____26456 =
                    let uu____26462 =
                      let uu____26464 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26466 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26468 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26470 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26464 uu____26466 uu____26468 uu____26470
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26462)
                     in
                  FStar_Errors.raise_error uu____26456
                    t1.FStar_Syntax_Syntax.pos
              | uu____26474 ->
                  let uu____26479 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26479 orig))))

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
          (let uu____26545 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26545
           then
             let uu____26550 =
               let uu____26552 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26552  in
             let uu____26553 =
               let uu____26555 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26555  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26550 uu____26553
           else ());
          (let uu____26559 =
             let uu____26561 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26561  in
           if uu____26559
           then
             let uu____26564 =
               mklstr
                 (fun uu____26571  ->
                    let uu____26572 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26574 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26572 uu____26574)
                in
             giveup env uu____26564 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26596 =
                  mklstr
                    (fun uu____26603  ->
                       let uu____26604 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26606 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26604 uu____26606)
                   in
                giveup env uu____26596 orig)
             else
               (let uu____26611 =
                  FStar_List.fold_left2
                    (fun uu____26632  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26632 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26653 =
                                 let uu____26658 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26659 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26658
                                   FStar_TypeChecker_Common.EQ uu____26659
                                   "effect universes"
                                  in
                               (match uu____26653 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26611 with
                | (univ_sub_probs,wl1) ->
                    let uu____26679 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26679 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26687 =
                           FStar_List.fold_right2
                             (fun uu____26724  ->
                                fun uu____26725  ->
                                  fun uu____26726  ->
                                    match (uu____26724, uu____26725,
                                            uu____26726)
                                    with
                                    | ((a1,uu____26770),(a2,uu____26772),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26805 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26805 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26687 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26832 =
                                  let uu____26835 =
                                    let uu____26838 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26838
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26835
                                   in
                                FStar_List.append univ_sub_probs uu____26832
                                 in
                              let guard =
                                let guard =
                                  let uu____26860 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26860  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3527_26869 = wl3  in
                                {
                                  attempting = (uu___3527_26869.attempting);
                                  wl_deferred = (uu___3527_26869.wl_deferred);
                                  ctr = (uu___3527_26869.ctr);
                                  defer_ok = (uu___3527_26869.defer_ok);
                                  smt_ok = (uu___3527_26869.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3527_26869.umax_heuristic_ok);
                                  tcenv = (uu___3527_26869.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26871 = attempt sub_probs wl5  in
                              solve env uu____26871))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26889 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26889
           then
             let uu____26894 =
               let uu____26896 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26896
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26898 =
               let uu____26900 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26900
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26894 uu____26898
           else ());
          (let uu____26905 =
             let uu____26910 =
               let uu____26915 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26915
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26910
               (fun uu____26932  ->
                  match uu____26932 with
                  | (c,g) ->
                      let uu____26943 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26943, g))
              in
           match uu____26905 with
           | (c12,g_lift) ->
               ((let uu____26947 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26947
                 then
                   let uu____26952 =
                     let uu____26954 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26954
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26956 =
                     let uu____26958 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26958
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26952 uu____26956
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3547_26968 = wl  in
                     {
                       attempting = (uu___3547_26968.attempting);
                       wl_deferred = (uu___3547_26968.wl_deferred);
                       ctr = (uu___3547_26968.ctr);
                       defer_ok = (uu___3547_26968.defer_ok);
                       smt_ok = (uu___3547_26968.smt_ok);
                       umax_heuristic_ok =
                         (uu___3547_26968.umax_heuristic_ok);
                       tcenv = (uu___3547_26968.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26969 =
                     let rec is_uvar t =
                       let uu____26983 =
                         let uu____26984 = FStar_Syntax_Subst.compress t  in
                         uu____26984.FStar_Syntax_Syntax.n  in
                       match uu____26983 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26988 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27003) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27009) ->
                           is_uvar t1
                       | uu____27034 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27068  ->
                          fun uu____27069  ->
                            fun uu____27070  ->
                              match (uu____27068, uu____27069, uu____27070)
                              with
                              | ((a1,uu____27114),(a2,uu____27116),(is_sub_probs,wl2))
                                  ->
                                  let uu____27149 = is_uvar a1  in
                                  if uu____27149
                                  then
                                    ((let uu____27159 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27159
                                      then
                                        let uu____27164 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27166 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27164 uu____27166
                                      else ());
                                     (let uu____27171 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27171 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26969 with
                   | (is_sub_probs,wl2) ->
                       let uu____27199 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27199 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27207 =
                              let uu____27212 =
                                let uu____27213 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27213
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27212
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27207 with
                             | (uu____27220,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27231 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27233 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27231 s uu____27233
                                    in
                                 let uu____27236 =
                                   let uu____27265 =
                                     let uu____27266 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27266.FStar_Syntax_Syntax.n  in
                                   match uu____27265 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27326 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27326 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27389 =
                                              let uu____27408 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27408
                                                (fun uu____27512  ->
                                                   match uu____27512 with
                                                   | (l1,l2) ->
                                                       let uu____27585 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27585))
                                               in
                                            (match uu____27389 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27690 ->
                                       let uu____27691 =
                                         let uu____27697 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27697)
                                          in
                                       FStar_Errors.raise_error uu____27691 r
                                    in
                                 (match uu____27236 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27773 =
                                        let uu____27780 =
                                          let uu____27781 =
                                            let uu____27782 =
                                              let uu____27789 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27789,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27782
                                             in
                                          [uu____27781]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27780
                                          (fun b  ->
                                             let uu____27805 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27807 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27809 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27805 uu____27807
                                               uu____27809) r
                                         in
                                      (match uu____27773 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27819 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27819
                                             then
                                               let uu____27824 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27833 =
                                                          let uu____27835 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27835
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27833) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27824
                                             else ());
                                            (let wl4 =
                                               let uu___3619_27843 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3619_27843.attempting);
                                                 wl_deferred =
                                                   (uu___3619_27843.wl_deferred);
                                                 ctr = (uu___3619_27843.ctr);
                                                 defer_ok =
                                                   (uu___3619_27843.defer_ok);
                                                 smt_ok =
                                                   (uu___3619_27843.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3619_27843.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3619_27843.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27868 =
                                                        let uu____27875 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27875, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27868) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27892 =
                                               let f_sort_is =
                                                 let uu____27902 =
                                                   let uu____27903 =
                                                     let uu____27906 =
                                                       let uu____27907 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27907.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27906
                                                      in
                                                   uu____27903.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27902 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27918,uu____27919::is)
                                                     ->
                                                     let uu____27961 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27961
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27994 ->
                                                     let uu____27995 =
                                                       let uu____28001 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28001)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27995 r
                                                  in
                                               let uu____28007 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28042  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28042
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28063 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28063
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28007
                                                in
                                             match uu____27892 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28088 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28088
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28089 =
                                                   let g_sort_is =
                                                     let uu____28099 =
                                                       let uu____28100 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28100.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28099 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28105,uu____28106::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28166 ->
                                                         let uu____28167 =
                                                           let uu____28173 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28173)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28167 r
                                                      in
                                                   let uu____28179 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28214  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28214
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28235
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28235
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28179
                                                    in
                                                 (match uu____28089 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28262 =
                                                          let uu____28267 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28268 =
                                                            let uu____28269 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28269
                                                             in
                                                          (uu____28267,
                                                            uu____28268)
                                                           in
                                                        match uu____28262
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28297 =
                                                          let uu____28300 =
                                                            let uu____28303 =
                                                              let uu____28306
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28306
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28303
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28300
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28297
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28330 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28330
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
                                                        let uu____28341 =
                                                          let uu____28344 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28347 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28347)
                                                            uu____28344
                                                           in
                                                        solve_prob orig
                                                          uu____28341 [] wl6
                                                         in
                                                      let uu____28348 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28348))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28371 =
            let univs =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28373 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28373]
              | x -> x  in
            let c12 =
              let uu___3685_28376 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3685_28376.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3685_28376.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3685_28376.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3685_28376.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28377 =
              let uu____28382 =
                FStar_All.pipe_right
                  (let uu___3688_28384 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3688_28384.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3688_28384.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3688_28384.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3688_28384.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28382
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28377
              (fun uu____28398  ->
                 match uu____28398 with
                 | (c,g) ->
                     let uu____28405 =
                       let uu____28407 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28407  in
                     if uu____28405
                     then
                       let uu____28410 =
                         let uu____28416 =
                           let uu____28418 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28420 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28418 uu____28420
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28416)
                          in
                       FStar_Errors.raise_error uu____28410 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28426 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28426
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28432 = lift_c1 ()  in
               solve_eq uu____28432 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___28_28441  ->
                         match uu___28_28441 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28446 -> false))
                  in
               let uu____28448 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28478)::uu____28479,(wp2,uu____28481)::uu____28482)
                     -> (wp1, wp2)
                 | uu____28555 ->
                     let uu____28580 =
                       let uu____28586 =
                         let uu____28588 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28590 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28588 uu____28590
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28586)
                        in
                     FStar_Errors.raise_error uu____28580
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28448 with
               | (wpc1,wpc2) ->
                   let uu____28600 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28600
                   then
                     let uu____28603 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28603 wl
                   else
                     (let uu____28607 =
                        let uu____28614 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28614  in
                      match uu____28607 with
                      | (c2_decl,qualifiers) ->
                          let uu____28635 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28635
                          then
                            let c1_repr =
                              let uu____28642 =
                                let uu____28643 =
                                  let uu____28644 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28644  in
                                let uu____28645 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28643 uu____28645
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28642
                               in
                            let c2_repr =
                              let uu____28648 =
                                let uu____28649 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28650 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28649 uu____28650
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28648
                               in
                            let uu____28652 =
                              let uu____28657 =
                                let uu____28659 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28661 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28659
                                  uu____28661
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28657
                               in
                            (match uu____28652 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28667 = attempt [prob] wl2  in
                                 solve env uu____28667)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28687 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28687
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28710 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28710
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
                                        let uu____28720 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28720 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28727 =
                                        let uu____28734 =
                                          let uu____28735 =
                                            let uu____28752 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28755 =
                                              let uu____28766 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28766; wpc1_2]  in
                                            (uu____28752, uu____28755)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28735
                                           in
                                        FStar_Syntax_Syntax.mk uu____28734
                                         in
                                      uu____28727
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
                                     let uu____28815 =
                                       let uu____28822 =
                                         let uu____28823 =
                                           let uu____28840 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28843 =
                                             let uu____28854 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28863 =
                                               let uu____28874 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28874; wpc1_2]  in
                                             uu____28854 :: uu____28863  in
                                           (uu____28840, uu____28843)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28823
                                          in
                                       FStar_Syntax_Syntax.mk uu____28822  in
                                     uu____28815 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28928 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28928
                              then
                                let uu____28933 =
                                  let uu____28935 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28935
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28933
                              else ());
                             (let uu____28939 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28939 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28948 =
                                      let uu____28951 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____28954  ->
                                           FStar_Pervasives_Native.Some
                                             uu____28954) uu____28951
                                       in
                                    solve_prob orig uu____28948 [] wl1  in
                                  let uu____28955 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28955))))
           in
        let uu____28956 = FStar_Util.physical_equality c1 c2  in
        if uu____28956
        then
          let uu____28959 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28959
        else
          ((let uu____28963 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28963
            then
              let uu____28968 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28970 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28968
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28970
            else ());
           (let uu____28975 =
              let uu____28984 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28987 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28984, uu____28987)  in
            match uu____28975 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29005),FStar_Syntax_Syntax.Total
                    (t2,uu____29007)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29024 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29024 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29026,FStar_Syntax_Syntax.Total uu____29027) ->
                     let uu____29044 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29044 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29048),FStar_Syntax_Syntax.Total
                    (t2,uu____29050)) ->
                     let uu____29067 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29067 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29070),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29072)) ->
                     let uu____29089 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29089 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29092),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29094)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29111 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29111 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29114),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29116)) ->
                     let uu____29133 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29133 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29136,FStar_Syntax_Syntax.Comp uu____29137) ->
                     let uu____29146 =
                       let uu___3812_29149 = problem  in
                       let uu____29152 =
                         let uu____29153 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29153
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3812_29149.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29152;
                         FStar_TypeChecker_Common.relation =
                           (uu___3812_29149.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3812_29149.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3812_29149.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3812_29149.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3812_29149.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3812_29149.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3812_29149.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3812_29149.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29146 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29154,FStar_Syntax_Syntax.Comp uu____29155) ->
                     let uu____29164 =
                       let uu___3812_29167 = problem  in
                       let uu____29170 =
                         let uu____29171 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29171
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3812_29167.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29170;
                         FStar_TypeChecker_Common.relation =
                           (uu___3812_29167.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3812_29167.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3812_29167.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3812_29167.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3812_29167.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3812_29167.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3812_29167.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3812_29167.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29164 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29172,FStar_Syntax_Syntax.GTotal uu____29173) ->
                     let uu____29182 =
                       let uu___3824_29185 = problem  in
                       let uu____29188 =
                         let uu____29189 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29189
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3824_29185.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3824_29185.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3824_29185.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29188;
                         FStar_TypeChecker_Common.element =
                           (uu___3824_29185.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3824_29185.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3824_29185.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3824_29185.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3824_29185.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3824_29185.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29182 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29190,FStar_Syntax_Syntax.Total uu____29191) ->
                     let uu____29200 =
                       let uu___3824_29203 = problem  in
                       let uu____29206 =
                         let uu____29207 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29207
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3824_29203.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3824_29203.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3824_29203.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29206;
                         FStar_TypeChecker_Common.element =
                           (uu___3824_29203.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3824_29203.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3824_29203.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3824_29203.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3824_29203.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3824_29203.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29200 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29208,FStar_Syntax_Syntax.Comp uu____29209) ->
                     let uu____29210 =
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
                     if uu____29210
                     then
                       let uu____29213 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29213 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29220 =
                            let uu____29225 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29225
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29234 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29235 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29234, uu____29235))
                             in
                          match uu____29220 with
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
                           (let uu____29243 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29243
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29251 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29251 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29254 =
                                  mklstr
                                    (fun uu____29261  ->
                                       let uu____29262 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29264 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29262 uu____29264)
                                   in
                                giveup env uu____29254 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29275 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29275 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29325 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29325 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29350 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29381  ->
                match uu____29381 with
                | (u1,u2) ->
                    let uu____29389 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29391 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29389 uu____29391))
         in
      FStar_All.pipe_right uu____29350 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29428,[])) when
          let uu____29455 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29455 -> "{}"
      | uu____29458 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29485 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29485
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29497 =
              FStar_List.map
                (fun uu____29510  ->
                   match uu____29510 with
                   | (uu____29517,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29497 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29528 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29528 imps
  
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
                  let uu____29585 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29585
                  then
                    let uu____29593 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29595 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29593
                      (rel_to_string rel) uu____29595
                  else "TOP"  in
                let uu____29601 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29601 with
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
              let uu____29661 =
                let uu____29664 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____29667  ->
                     FStar_Pervasives_Native.Some uu____29667) uu____29664
                 in
              FStar_Syntax_Syntax.new_bv uu____29661 t1  in
            let uu____29668 =
              let uu____29673 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29673
               in
            match uu____29668 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29731 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29731
         then
           let uu____29736 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29736
         else ());
        (let uu____29743 =
           FStar_Util.record_time (fun uu____29750  -> solve env probs)  in
         match uu____29743 with
         | (sol,ms) ->
             ((let uu____29762 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29762
               then
                 let uu____29767 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29767
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29780 =
                     FStar_Util.record_time
                       (fun uu____29787  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29780 with
                    | ((),ms1) ->
                        ((let uu____29798 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29798
                          then
                            let uu____29803 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29803
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29815 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29815
                     then
                       let uu____29822 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29822
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
          ((let uu____29848 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29848
            then
              let uu____29853 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29853
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29861 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29861
             then
               let uu____29866 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29866
             else ());
            (let f2 =
               let uu____29872 =
                 let uu____29873 = FStar_Syntax_Util.unmeta f1  in
                 uu____29873.FStar_Syntax_Syntax.n  in
               match uu____29872 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29877 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3941_29878 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3941_29878.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3941_29878.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3941_29878.FStar_TypeChecker_Common.implicits)
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
            let uu____29921 =
              let uu____29922 =
                let uu____29923 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____29924  ->
                       FStar_TypeChecker_Common.NonTrivial uu____29924)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29923;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29922  in
            FStar_All.pipe_left
              (fun uu____29931  -> FStar_Pervasives_Native.Some uu____29931)
              uu____29921
  
let with_guard_no_simp :
  'uuuuuu29941 .
    'uuuuuu29941 ->
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
            let uu____29981 =
              let uu____29982 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____29983  ->
                     FStar_TypeChecker_Common.NonTrivial uu____29983)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29982;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29981
  
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
          (let uu____30016 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30016
           then
             let uu____30021 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30023 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30021
               uu____30023
           else ());
          (let uu____30028 =
             let uu____30033 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30033
              in
           match uu____30028 with
           | (prob,wl) ->
               let g =
                 let uu____30041 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30049  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30041  in
               ((let uu____30067 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30067
                 then
                   let uu____30072 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30072
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
        let uu____30093 = try_teq true env t1 t2  in
        match uu____30093 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30098 = FStar_TypeChecker_Env.get_range env  in
              let uu____30099 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30098 uu____30099);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30107 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30107
              then
                let uu____30112 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30114 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30116 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30112
                  uu____30114 uu____30116
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
        (let uu____30140 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30140
         then
           let uu____30145 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30147 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30145
             uu____30147
         else ());
        (let uu____30152 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30152 with
         | (prob,x,wl) ->
             let g =
               let uu____30167 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30176  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30167  in
             ((let uu____30194 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30194
               then
                 let uu____30199 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30199
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30207 =
                     let uu____30208 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30208 g1  in
                   FStar_Pervasives_Native.Some uu____30207)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30230 = FStar_TypeChecker_Env.get_range env  in
          let uu____30231 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30230 uu____30231
  
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
        (let uu____30260 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30260
         then
           let uu____30265 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30267 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30265 uu____30267
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30278 =
           let uu____30285 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30285 "sub_comp"
            in
         match uu____30278 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30298 =
                 FStar_Util.record_time
                   (fun uu____30310  ->
                      let uu____30311 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30320  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30311)
                  in
               match uu____30298 with
               | (r,ms) ->
                   ((let uu____30348 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30348
                     then
                       let uu____30353 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30355 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30357 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30353 uu____30355
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30357
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
      fun uu____30395  ->
        match uu____30395 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30438 =
                 let uu____30444 =
                   let uu____30446 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30448 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30446 uu____30448
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30444)  in
               let uu____30452 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30438 uu____30452)
               in
            let equiv v v' =
              let uu____30465 =
                let uu____30470 = FStar_Syntax_Subst.compress_univ v  in
                let uu____30471 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30470, uu____30471)  in
              match uu____30465 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30491 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____30522 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____30522 with
                      | FStar_Syntax_Syntax.U_unif uu____30529 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30558  ->
                                    match uu____30558 with
                                    | (u,v') ->
                                        let uu____30567 = equiv v v'  in
                                        if uu____30567
                                        then
                                          let uu____30572 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____30572 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____30593 -> []))
               in
            let uu____30598 =
              let wl =
                let uu___4052_30602 = empty_worklist env  in
                {
                  attempting = (uu___4052_30602.attempting);
                  wl_deferred = (uu___4052_30602.wl_deferred);
                  ctr = (uu___4052_30602.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4052_30602.smt_ok);
                  umax_heuristic_ok = (uu___4052_30602.umax_heuristic_ok);
                  tcenv = (uu___4052_30602.tcenv);
                  wl_implicits = (uu___4052_30602.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30621  ->
                      match uu____30621 with
                      | (lb,v) ->
                          let uu____30628 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____30628 with
                           | USolved wl1 -> ()
                           | uu____30631 -> fail lb v)))
               in
            let rec check_ineq uu____30642 =
              match uu____30642 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30654) -> true
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
                      uu____30678,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30680,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30691) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____30699,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____30708 -> false)
               in
            let uu____30714 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30731  ->
                      match uu____30731 with
                      | (u,v) ->
                          let uu____30739 = check_ineq (u, v)  in
                          if uu____30739
                          then true
                          else
                            ((let uu____30747 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30747
                              then
                                let uu____30752 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30754 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____30752
                                  uu____30754
                              else ());
                             false)))
               in
            if uu____30714
            then ()
            else
              ((let uu____30764 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30764
                then
                  ((let uu____30770 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30770);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30782 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30782))
                else ());
               (let uu____30795 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30795))
  
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
        let fail uu____30868 =
          match uu____30868 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4129_30891 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4129_30891.attempting);
            wl_deferred = (uu___4129_30891.wl_deferred);
            ctr = (uu___4129_30891.ctr);
            defer_ok;
            smt_ok = (uu___4129_30891.smt_ok);
            umax_heuristic_ok = (uu___4129_30891.umax_heuristic_ok);
            tcenv = (uu___4129_30891.tcenv);
            wl_implicits = (uu___4129_30891.wl_implicits)
          }  in
        (let uu____30894 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30894
         then
           let uu____30899 = FStar_Util.string_of_bool defer_ok  in
           let uu____30901 = wl_to_string wl  in
           let uu____30903 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30899 uu____30901 uu____30903
         else ());
        (let g1 =
           let uu____30909 = solve_and_commit env wl fail  in
           match uu____30909 with
           | FStar_Pervasives_Native.Some
               (uu____30916::uu____30917,uu____30918) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4144_30947 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4144_30947.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4144_30947.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30948 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4149_30957 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4149_30957.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4149_30957.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4149_30957.FStar_TypeChecker_Common.implicits)
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
            let uu___4161_31034 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4161_31034.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4161_31034.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4161_31034.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31035 =
            let uu____31037 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31037  in
          if uu____31035
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug
                  then
                    (let uu____31049 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31050 =
                       let uu____31052 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31052
                        in
                     FStar_Errors.diag uu____31049 uu____31050)
                  else ();
                  (let vc1 =
                     let uu____31058 =
                       let uu____31062 =
                         let uu____31064 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31064  in
                       FStar_Pervasives_Native.Some uu____31062  in
                     FStar_Profiling.profile
                       (fun uu____31067  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31058 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug
                   then
                     (let uu____31071 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31072 =
                        let uu____31074 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31074
                         in
                      FStar_Errors.diag uu____31071 uu____31072)
                   else ();
                   (let uu____31080 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31080
                      "discharge_guard'" env vc1);
                   (let uu____31082 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31082 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug
                           then
                             (let uu____31091 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31092 =
                                let uu____31094 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31094
                                 in
                              FStar_Errors.diag uu____31091 uu____31092)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug
                           then
                             (let uu____31104 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31105 =
                                let uu____31107 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31107
                                 in
                              FStar_Errors.diag uu____31104 uu____31105)
                           else ();
                           (let vcs =
                              let uu____31121 = FStar_Options.use_tactics ()
                                 in
                              if uu____31121
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31143  ->
                                     (let uu____31145 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        (fun uu____31147  -> ()) uu____31145);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31190  ->
                                              match uu____31190 with
                                              | (env1,goal,opts) ->
                                                  let uu____31206 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31206, opts)))))
                              else
                                (let uu____31210 =
                                   let uu____31217 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31217)  in
                                 [uu____31210])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31250  ->
                                    match uu____31250 with
                                    | (env1,goal,opts) ->
                                        let uu____31260 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31260 with
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
                                                (let uu____31271 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31272 =
                                                   let uu____31274 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31276 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31274 uu____31276
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31271 uu____31272)
                                              else ();
                                              if debug
                                              then
                                                (let uu____31283 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31284 =
                                                   let uu____31286 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31286
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31283 uu____31284)
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
      let uu____31304 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31304 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31313 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31313
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31327 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31327 with
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
        let uu____31357 = try_teq false env t1 t2  in
        match uu____31357 with
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
            let uu____31401 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31401 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31414 ->
                     let uu____31427 =
                       let uu____31428 = FStar_Syntax_Subst.compress r  in
                       uu____31428.FStar_Syntax_Syntax.n  in
                     (match uu____31427 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31433) ->
                          unresolved ctx_u'
                      | uu____31450 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31474 = acc  in
            match uu____31474 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____31493 = hd  in
                     (match uu____31493 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____31504 = unresolved ctx_u  in
                             if uu____31504
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd :: out), changed) tl
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31528 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31528
                                     then
                                       let uu____31532 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31532
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31541 = teq_nosmt env1 t tm
                                          in
                                       match uu____31541 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4274_31551 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4274_31551.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4274_31551.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4274_31551.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4274_31551.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4274_31551.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4274_31551.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4274_31551.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4277_31559 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4277_31559.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4277_31559.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4277_31559.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4281_31570 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4281_31570.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4281_31570.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4281_31570.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4281_31570.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4281_31570.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4281_31570.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4281_31570.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4281_31570.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4281_31570.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4281_31570.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4281_31570.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4281_31570.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4281_31570.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4281_31570.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4281_31570.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4281_31570.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4281_31570.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4281_31570.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4281_31570.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4281_31570.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4281_31570.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4281_31570.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4281_31570.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4281_31570.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4281_31570.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4281_31570.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4281_31570.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4281_31570.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4281_31570.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4281_31570.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4281_31570.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4281_31570.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4281_31570.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4281_31570.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4281_31570.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4281_31570.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4281_31570.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4281_31570.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4281_31570.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4281_31570.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4281_31570.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4281_31570.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4281_31570.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4281_31570.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4281_31570.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4286_31575 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4286_31575.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4286_31575.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4286_31575.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4286_31575.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4286_31575.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4286_31575.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4286_31575.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4286_31575.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4286_31575.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4286_31575.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4286_31575.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4286_31575.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4286_31575.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4286_31575.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4286_31575.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4286_31575.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4286_31575.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4286_31575.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4286_31575.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4286_31575.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4286_31575.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4286_31575.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4286_31575.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4286_31575.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4286_31575.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4286_31575.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4286_31575.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4286_31575.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4286_31575.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4286_31575.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4286_31575.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4286_31575.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4286_31575.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4286_31575.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4286_31575.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4286_31575.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4286_31575.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31580 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31580
                                   then
                                     let uu____31585 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31587 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31589 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31591 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31585 uu____31587 uu____31589
                                       reason uu____31591
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4292_31598  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31605 =
                                             let uu____31615 =
                                               let uu____31623 =
                                                 let uu____31625 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31627 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31629 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31625 uu____31627
                                                   uu____31629
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31623, r)
                                                in
                                             [uu____31615]  in
                                           FStar_Errors.add_errors
                                             uu____31605);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31648 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31659  ->
                                               let uu____31660 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31662 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31664 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31660 uu____31662
                                                 reason uu____31664)) env2 g1
                                         true
                                        in
                                     match uu____31648 with
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
          let uu___4304_31672 = g  in
          let uu____31673 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4304_31672.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4304_31672.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4304_31672.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31673
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
        let uu____31713 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31713 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31714 = discharge_guard env g1  in
          FStar_All.pipe_left (fun uu____31715  -> ()) uu____31714
      | imp::uu____31717 ->
          let uu____31720 =
            let uu____31726 =
              let uu____31728 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31730 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31728 uu____31730
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31726)
             in
          FStar_Errors.raise_error uu____31720
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31750 = teq env t1 t2  in
        force_trivial_guard env uu____31750
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31769 = teq_nosmt env t1 t2  in
        match uu____31769 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4329_31788 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4329_31788.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4329_31788.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4329_31788.FStar_TypeChecker_Common.implicits)
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
        (let uu____31824 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31824
         then
           let uu____31829 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31831 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31829
             uu____31831
         else ());
        (let uu____31836 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31836 with
         | (prob,x,wl) ->
             let g =
               let uu____31855 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31864  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31855  in
             ((let uu____31882 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31882
               then
                 let uu____31887 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31889 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31891 =
                   let uu____31893 = FStar_Util.must g  in
                   guard_to_string env uu____31893  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31887 uu____31889 uu____31891
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
        let uu____31930 = check_subtyping env t1 t2  in
        match uu____31930 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31949 =
              let uu____31950 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31950 g  in
            FStar_Pervasives_Native.Some uu____31949
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31969 = check_subtyping env t1 t2  in
        match uu____31969 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31988 =
              let uu____31989 =
                let uu____31990 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31990]  in
              FStar_TypeChecker_Env.close_guard env uu____31989 g  in
            FStar_Pervasives_Native.Some uu____31988
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32028 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32028
         then
           let uu____32033 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32035 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32033
             uu____32035
         else ());
        (let uu____32040 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32040 with
         | (prob,x,wl) ->
             let g =
               let uu____32055 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32064  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32055  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32085 =
                      let uu____32086 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32086]  in
                    FStar_TypeChecker_Env.close_guard env uu____32085 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32127 = subtype_nosmt env t1 t2  in
        match uu____32127 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  